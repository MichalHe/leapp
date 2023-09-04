from collections import defaultdict
import functools
import itertools
import json
import logging
import os
import sys

from leapp.exceptions import LeappError
from leapp.models import get_models
from leapp.repository.scan import find_and_scan_repositories
from leapp.snactor.utils import safe_discover
from leapp.tags import get_tags
from leapp.topics import get_topics
from leapp.utils.clicmd import command, command_opt
from leapp.utils.repository import find_repository_basedir, get_repository_name, requires_repository
from leapp.workflows import get_workflows


def _is_local(repository, cls, base_dir, all_repos=False):
    cls_path = os.path.realpath(sys.modules[cls.__module__].__file__)
    if all_repos:
        return any((cls_path.startswith(repo.repo_dir) for repo in repository.repos))
    return cls_path.startswith(base_dir)


def _get_class_file(cls, repository_relative=True):
    path = os.path.abspath(sys.modules[cls.__module__].__file__.replace('.pyc', '.py'))
    return os.path.relpath(path, find_repository_basedir('.') if repository_relative else os.getcwd())


def _print_group(name, items, name_resolver=lambda i: i.__name__, path_resolver=_get_class_file):
    sys.stdout.write('{group}({count}):\n'.format(group=name, count=len(items)))
    for item in sorted(items, key=name_resolver):
        sys.stdout.write('   - {name:<35} {path}\n'.format(name=name_resolver(item), path=path_resolver(item, False)))
    sys.stdout.write('\n')


def _get_actor_path(actor, repository_relative=True):
    path = actor.directory
    return os.path.relpath(path, find_repository_basedir('.') if repository_relative else os.getcwd())


def _get_actor_details(actor):
    meta = actor.discover()
    meta['produces'] = tuple(model.__name__ for model in actor.produces)
    meta['consumes'] = tuple(model.__name__ for model in actor.consumes)
    meta['apis'] = tuple(api.serialize() for api in actor.apis)
    meta['tags'] = tuple(tag.name for tag in meta['tags'])
    meta['path'] = _get_class_file(actor)
    meta['dialogs'] = [dialog.serialize() for dialog in actor.dialogs]
    return meta


def _get_workflow_details(workflow):
    return workflow.serialize()


def _get_tag_details(tag):
    return {'actors': [actor.class_name for actor in tag.actors],
            'name': tag.name}


def _get_topic_details(topic):
    return {'name': topic().name,
            'path': _get_class_file(topic)}


def _get_model_details(model):
    return {'path': _get_class_file(model)}


_LONG_DESCRIPTION = '''
Discovers and displays supported entities from the current repository.

Support entities:
- Actors
- Models
- Tags
- Topics
- Workflows


For more information please consider reading the documentation at:
https://red.ht/leapp-docs
'''


class RepositoryGraph(object):
    def __init__(self):
        # The graph is stored as:
        # source_actor -> destination_actor -> [message types]
        self.edges = defaultdict(functools.partial(defaultdict, set))
        self.reverse_edges = defaultdict(set)
        self.actors = set()

    def add_edge(self, source_actor, msg, target_actor):
        self.actors.add(source_actor)
        self.actors.add(target_actor)
        self.edges[source_actor][target_actor].add(msg)
        self.reverse_edges[target_actor].add(source_actor)

    def iter_edges(self):
        """ Iterate over graph edges in the form of (source_actor, message_type, target_actor) """
        for source_actor, target_actors in self.edges.items():
            for target_actor, edge_msgs in target_actors.items():
                for edge_msg in edge_msgs:
                    yield (source_actor, edge_msg, target_actor)

    def into_dot(self):
        # Prepare the graph description manually to avoid introducing snactor dependency
        header = ('digraph "leapp-actors" {\n'
                  'nodesep=2\n'
                  'ranksep=2\n'
                  'rankdir=LR')
        footer = '}'
        node_declarations = ['{0} [label={0}]'.format(actor) for actor in self.actors]
        edge_declarations = [
            '{source} -> {target} [label={msg}]'.format(source=source, target=target, msg=msg_type)
            for source, msg_type, target in self.iter_edges()
        ]

        return '{header}\n {nodes}\n {edges}\n {footer}\n'.format(header=header, nodes='\n'.join(node_declarations),
                                                                  edges='\n'.join(edge_declarations), footer=footer)

    def _collect_actors_for_entities(self, leapp_entities):
        forward_actors = set()
        backward_actors = set()
        for leapp_entity in leapp_entities:
            if leapp_entity in self.actors:
                forward_actors.add(leapp_entity)
                backward_actors.add(leapp_entity)
            else:
                msg_type = leapp_entity

                for source_actor, target_actors in self.edges.items():
                    for target_actor, msgs in target_actors.items():
                        if msg_type in msgs:
                            backward_actors.add(source_actor)
                            forward_actors.add(target_actor)

        return forward_actors, backward_actors

    def _dfs_graph_scan(self, start_at_actors):  # Ignores graph edge directions
        worklist = list(start_at_actors)
        visited_actors = set(start_at_actors)

        while worklist:
            actor = worklist.pop(-1)

            for target_actor in self.edges[actor]:
                if target_actor not in visited_actors:
                    visited_actors.add(target_actor)
                    worklist.append(target_actor)

            for source_actor in self.reverse_edges[actor]:
                if source_actor not in visited_actors:
                    visited_actors.add(source_actor)
                    worklist.append(source_actor)
        return visited_actors

    def _forward_scan(self, start_at_actors):
        worklist = list(start_at_actors)
        visited_actors = set(start_at_actors)

        while worklist:
            actor = worklist.pop(-1)

            for target_actor in self.edges[actor]:
                if target_actor not in visited_actors:
                    visited_actors.add(target_actor)
                    worklist.append(target_actor)

        return visited_actors

    def _backward_scan(self, start_at_actors):
        worklist = list(start_at_actors)
        visited_actors = set(start_at_actors)

        while worklist:
            actor = worklist.pop(-1)

            for source_actor in self.reverse_edges[actor]:
                if source_actor not in visited_actors:
                    visited_actors.add(source_actor)
                    worklist.append(source_actor)

        return visited_actors

    def make_subgraph_related_to(self, leapp_entities, tight=False):
        start_forward_at_actors, start_backward_at_actors = self._collect_actors_for_entities(leapp_entities)
        if tight:
            seen_actors = self._forward_scan(start_forward_at_actors)
            seen_actors.update(self._backward_scan(start_backward_at_actors))
        else:
            start_at_actors = start_forward_at_actors.union(start_backward_at_actors)
            seen_actors = self._dfs_graph_scan(start_at_actors)

        resulting_graph = RepositoryGraph()
        for source_actor, target_actors in self.edges.items():
            if source_actor not in seen_actors:
                continue
            for target_actor, msgs in target_actors.items():
                if target_actor not in seen_actors:
                    continue
                resulting_graph.edges[source_actor][target_actor] = set(msgs)
                resulting_graph.reverse_edges[target_actor].add(source_actor)
        resulting_graph.actors = seen_actors
        return resulting_graph


def construct_graph_from_actors(actor_definitions):
    producers_table = defaultdict(set)  # maps message_type to producers
    consumers_table = defaultdict(set)  # maps message_type to consumers

    for actor_def in actor_definitions:
        actor_name = actor_def.class_name
        for produced_message in actor_def.produces:
            msg_type = produced_message.__name__
            producers_table[msg_type].add(actor_name)
        for consumed_message in actor_def.consumes:
            msg_type = consumed_message.__name__
            consumers_table[msg_type].add(actor_name)

    spoken_messages = set(producers_table.keys()).intersection(consumers_table.keys())

    graph = RepositoryGraph()

    for msg_type in spoken_messages:
        consumers = consumers_table[msg_type]
        producers = producers_table[msg_type]

        for consumer, producer in itertools.product(consumers, producers):
            graph.add_edge(producer, msg_type, consumer)

    return graph


@command('discover', help="Discovers all available entities in the current repository",
         description=_LONG_DESCRIPTION)
@command_opt('json', is_flag=True, help='Output in json format instead of human readable form')
@command_opt('all', is_flag=True, help='Include items from linked repositories')
@command_opt('safe', is_flag=True, help='Analyze actor files statically to work around runtime errors')
@command_opt('as-graph', is_flag=True, help='Export repository information as a DOT graph')
@command_opt('only-related-to', short_name='f', action='append', default=[],
             help='Export repository information only related to the given entity')
@command_opt('tight', is_flag=True, help='Do not include actors that indirectly relate to entities')
@requires_repository
def cli(args):
    logging.basicConfig(level=logging.WARNING, stream=sys.stderr)
    base_dir = find_repository_basedir('.')

    if args.safe and args.json:
        sys.stderr.write('The options --safe and --json are currently mutually exclusive\n')
        sys.exit(1)

    if args.safe:
        sys.stdout.write(
            'Repository:\n  Name: {repository}\n  Path: {base_dir}\n\n'.format(repository=get_repository_name(base_dir),
                                                                               base_dir=base_dir))
        safe_discover(base_dir)
        sys.exit(0)

    repository = find_and_scan_repositories(base_dir, include_locals=True)
    try:
        repository.load()
    except LeappError as exc:
        sys.stderr.write(exc.message)
        sys.stderr.write('\n')
        sys.exit(1)

    actors = repository.actors
    topics = [topic for topic in get_topics() if _is_local(repository, topic, base_dir, all_repos=args.all)]
    models = [model for model in get_models() if _is_local(repository, model, base_dir, all_repos=args.all)]
    tags = [tag for tag in get_tags() if _is_local(repository, tag, base_dir, all_repos=args.all)]
    workflows = [workflow for workflow in get_workflows() if _is_local(repository, workflow, base_dir,
                                                                       all_repos=args.all)]

    if args.as_graph:
        graph = construct_graph_from_actors(actors)
        if args.only_related_to:
            entities = args.only_related_to
            graph = graph.make_subgraph_related_to(entities, tight=args.tight)
        print(graph.into_dot())
    elif not args.json:
        sys.stdout.write(
            'Repository:\n  Name: {repository}\n  Path: {base_dir}\n\n'.format(repository=get_repository_name(base_dir),
                                                                               base_dir=base_dir))
        _print_group('Actors', actors, name_resolver=lambda x: x.class_name, path_resolver=_get_actor_path)
        _print_group('Models', models)
        _print_group('Tags', tags)
        _print_group('Topics', topics)
        _print_group('Workflows', workflows)
    else:
        output = {
            'repository': get_repository_name(base_dir),
            'base_dir': base_dir,
            'topics': dict((topic.__name__, _get_topic_details(topic)) for topic in topics),
            'models': dict((model.__name__, _get_model_details(model)) for model in models),
            'actors': dict((actor.class_name, _get_actor_details(actor)) for actor in actors),
            'tags': dict((tag.name, _get_tag_details(tag)) for tag in tags),
            'workflows': dict((workflow.__name__, _get_workflow_details(workflow)) for workflow in workflows)
        }
        json.dump(output, sys.stdout, indent=2)
        sys.stdout.write('\n')
