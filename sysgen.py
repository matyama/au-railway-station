__author__ = 'matyama2'

import os
import sys
import getopt
import networkx as nx

from subprocess import call
from collections import deque
from itertools import product, combinations, chain, tee

# station docs
TRAIN_DOCS = "\n% each train must go somewhere eventually:\n% ----------------------------------------\n" \
             "% if X is a train, there exists a future time T2 such that the train will 'go' at this time point\n\n"
AT_DOCS = "\n\n% train movement axioms:\n% ----------------------\n" \
          "% (i) train X is 'at' an input node at time T+1 iff \n% \tit either 'enter'ed at that node at time T or " \
          "it was already there and either didn't 'go' or the gate didn't 'open'\n" \
          "% (ii) train X is 'at' an output node at time T+1 iff \n" \
          "% \tit was 'at' adjacent node and the switch was properly set\n" \
          "% (iii) train X is 'at' a switch at time T+1 iff\n% \tit either was 'at' an adjacent (properly set) node " \
          "or it was already there and didn't 'go'\n\n"
TRAIN_EXIT_DOCS = "\n\n% each train must leave an output node:\n% -------------------------------------\n" \
                  "% if a train is at some time 'at' an output node, it can't be there at the next time point\n\n"
AT_UNIQUENESS_DOCS = "\n\n% at predicate uniqueness:\n% ------------------------\n" \
                     "% each train X can be only 'at' one place at a time T\n\n"
TRAIN_UNIQUENESS_DOCS = "\n\n% train uniqueness:\n% -----------------\n" \
                        "% if a train X is 'at' some node N1, it cannot 'enter' again at some input gate N2\n\n"
ENTER_SAFETY_DOCS = "\n\n% enter safety:\n% -------------\n" \
                    "% if a train X is 'at' input node N at time T, no other train Y can 'enter' N at the same time\n\n"
ENTER_UNIQUENESS_DOCS = "\n\n% enter uniqueness:\n% ----------------\n" \
                        "% no two trains X, Y can 'enter' the same input node N at the same time T\n\n"
AT_RESTRICTION_DOCS = "\n\n% at predicate restriction:\n% -------------------------\n" \
                      "% node variable in predicate 'at' can take value only from domain of nodes\n\n"
NODE_EXCLUSIVITY_DOCS = "\n\n% all nodes must be different:\n% ----------------------------\n" \
                        "% each node-related constant symbol must be pairwise different\n\n"

# consistency docs
GO_IF_POSSIBLE_DOCS = "% go if possible axiom:\n% ---------------------\n" \
                      "% generate 'go' predicate for all times and trains\n" \
                      "% using this and other 'go'-related axioms, the train will move as soon as possible\n\n"
ENTER_GENERATOR_DOCS = "\n\n% enter generator axioms:\n% -----------------------\n" \
                       "% for each time T there is a train X that 'enter's at an input gate\n\n"

# control system docs
INPUT_CYCLE_DOCS = "\n% inputs cyclically change in time:\n% ---------------------------------\n" \
                   "% given input nodes in_1, ..., in_n, if input(T) = in_i then input(T+1) = in_{i+1} (modulo n)\n\n"
INPUT_CYCLE_DEFINEDNESS_DOCS = "\n\n% definedness of input cycling:\n% -----------------------------\n" \
                               "% function symbol 'input' must take at least one value from the domain of " \
                               "input nodes for each time T\n\n"
PATH_SWITCHED_DOCS = "\n\n% switch configuration axioms:\n% ----------------------------\n" \
                     "% path is called to be 'switched' at certain time iff \n" \
                     "% all relevant switch nodes are set in such way that a train can pass the path\n\n"
FREE_PATH_DOCS = "\n\n% free path axioms:\n% -----------------\n% path is called to be 'free' iff " \
                 "no inner node on the path is occupied by a train at certain time\n\n"
SAFE_PATH_DOCS = "\n\n% safe (non-conflicting) path axioms:\n% -----------------------------------\n" \
                 "% path is called to be 'safe' iff itself is 'free' and all conflicting paths are 'free'\n\n"
PATH_AVAILABLE_DOCS = "\n\n% path availability axiom:\n% ------------------------\n" \
                      "% path P is called to be 'available' iff it is 'safe' and 'switched'\n\n"
AVAILABLE_RESTRICTION_DOCS = "\n\n% available predicate restriction:\n% --------------------------------\n" \
                             "% path variable in predicate 'available' can take value only from domain of paths\n\n"
TRAIN_SIGNAL_DOCS = "\n\n% train driver signals:\n% ---------------------\n" \
                    "% train driver signals his/her desire to follow a route\n" \
                    "% defines predicate 'signal' for each time point and pair of input-output nodes to be true iff\n" \
                    "% there is a train X 'at' that input node and has that output node as 'dest(X)' at the time \n\n"
SIGNAL_RESTRICTION_DOCS = "\n\n% signal predicate restriction:\n% -----------------------------\n" \
                          "% restrict input and output nodes in predicate 'signal' to pairs of in-out nodes\n\n"
PATH_SELECTION_DOCS = "\n\n% path selection axioms:\n% ----------------------\n% path is 'selected' iff " \
                      "a train driver 'signal's he/she wants to follow it, is 'available' and 'open'\n\n"
PATH_CONTROL_DOCS = "\n\n% path control axiom:\n% -------------------\n" \
                    "% path is 'switched' in the next time iff it is 'selected'\n" \
                    "% or has been 'switched' and is being used (is not 'free')\n\n"
INPUT_CONTROL_DOCS = "\n\n% input gate control axioms:\n% --------------------------\n" \
                     "% input gates are 'open' iff some relevant path has been 'selected'\n\n"
TRAIN_DESTINATION_DOCS = "\n\n% each train has certain output as destination:\n" \
                         "% ---------------------------------------------\n" \
                         "% function symbol 'dest' takes at least one value from the domain of output nodes " \
                         "for each train X \n% (definedness of function symbol 'dest')\n\n"
PATH_EXCLUSIVITY_DOCS = "\n\n% all paths must be different:\n% ----------------------------\n" \
                        "% each path-related constant symbol must be pairwise different\n\n"
OPEN_RESTRICTION_DOCS = "\n\n% open predicate restriction:\n% ---------------------------\n" \
                        "% node variable in predicate 'open' can take value only from domain of input gates\n\n"

# critical state check docs
NO_CRASH_DOCS = "\n% no crash axiom:\n% ---------------\n% there is no crash on node N at time T iff " \
                "for each pair of trains X, Y holds:\n% if the trains are different and X is 'at' node N at T, " \
                "Y cannot be 'at' N at the same time\n\n"
NO_CRASH_RESTRICTION_DOCS = "\n\n% nocrash predicate restriction:\n% ------------------------------\n" \
                            "% node variable in predicate 'nocrash' can take value only from domain of nodes\n\n"
CRASH_CHECK_DOCS = "\n\n% no crash conjecture:\n% --------------------\n\n"
NO_DERAIL_DOCS = "\n% no derail axiom:\n% ----------------\n% there is no derail on node N iff " \
                 "for each time T and train X holds:\n% if X is 'at' node N at T and T+1 as well, " \
                 "then switch on N at T must be set to the same node as at T+1\n\n"
DERAIL_CHECK_DOCS = "\n\n% no derail conjecture:\n% ---------------------\n\n"
NO_BLOCK_DOCS = "\n% no block axiom:\n% ---------------\n% there is no block on node N iff " \
                "for each train X and time T1 holds:\n% if X is 'at' node N at T and the gate at N is not 'open', " \
                "then there must exist some future time T2 (T1 < T2)\n% such that the gate N at T2 will be 'open' \n\n"
OPEN_CHECK_DOCS = "\n\n% no block conjecture:\n% --------------------\n\n"

# order axioms
ANTISYMMETRY_AXIOM = 'fof(antisymmetry, axiom, (\n\t![X,Y]: ((less(X,Y) & less(Y,X)) => (X = Y))\n)).\n'
TRANSITIVITY_AXIOM = 'fof(transitivity, axiom, (\n\t![X,Y,Z]: ((less(X,Y) & less(Y,Z)) => less(X,Z))\n)).\n'
TOTALITY_AXIOM = 'fof(totality, axiom, (\n\t![X,Y]: (less(X,Y) | less(Y,X))\n)).\n'

# time-related successor/predecessor axioms
SUCCESSOR_AXIOM = 'fof(succ, axiom, (\n\t![X]: ((less(X,succ(X))) & (![Y]: (less(Y,X) | less(succ(X),Y))))\n)).\n'
PREDECESSOR_AXIOM = 'fof(pred, axiom, (\n\t![X]: (((pred(succ(X)) = X) & (succ(pred(X)) = X)))\n)).\n'

# station physics axiom
TRAIN_AXIOM = 'fof(train_axiom, axiom, (\n\t![X]: (train(X) => (![T1]: ?[T2]: (less(T1,T2) & go(T2,X))))\n)).\n'
AT_INPUT_AXIOM = 'fof(at_%s, axiom, (\n\t![T,X]: ' \
                 '(at(succ(T),X,%s) <=> (train(X) & (enter(T,X,%s) | (at(T,X,%s) & (~go(T,X) | ~open(T,%s))))))\n)).\n'
AT_OUTPUT_AXIOM = 'fof(at_%s, axiom, (\n\t' \
                  '![T,X]: (at(succ(T),X,%s) <=> (train(X) & go(T,X) & (%s)))\n)).\n'
AT_OTHER_AXIOM = 'fof(at_%s, axiom, (\n\t![T,X]: ' \
                 '(at(succ(T),X,%s) <=> ((train(X) & go(T,X) & (%s)) | (train(X) & ~go(T,X) & at(T,X,%s))))\n)).\n'
TRAIN_EXIT_AXIOM = 'fof(train_exits_%s, axiom, (\n\t![T,X]: (at(T,X,%s) => (~at(succ(T),X,%s)))\n)).\n'
AT_UNIQUENESS_AXIOM = 'fof(at_uniqueness, axiom, (\n\t' \
                      '![T,X,N1,N2]: ((at(T,X,N1) & at(T,X,N2)) => (N1 = N2))\n)).\n'
TRAIN_UNIQUENESS_AXIOM = 'fof(train_uniqueness, axiom, (\n\t![T,X,N1,N2]: (at(T,X,N1) => ~enter(T,X,N2))\n)).\n'
ENTER_SAFETY_AXIOM = 'fof(enter_safety, axiom, (\n\t![T,X,Y,N]: (at(T,X,N) => ~enter(T,Y,N))\n)).\n'
ENTER_UNIQUENESS_AXIOM = 'fof(enter_uniqueness, axiom, (\n\t' \
                         '![T,X,Y,N]: ((enter(T,X,N) & enter(T,Y,N)) => (X = Y))\n)).\n'
AT_RESTRICTION_AXIOM = 'fof(at_restriction_axiom, axiom, (\n\t![T,X,N]: (at(T,X,N) => (%s))\n)).\n'
NODE_EXCLUSIVITY_AXIOM = 'fof(node_exclusivity, axiom, (\n\t%s\n)).\n'

# consistency axioms
GO_IF_POSSIBLE_AXIOM = 'fof(go_if_possible, axiom, (\n\t![T,X]: go(T,X)\n)).\n'
ENTER_GENERATOR_AXIOM = 'fof(enter_generator_%s, axiom, (\n\t![T]:?[X]: enter(T,X,%s)\n)).\n'

# control system axioms
INPUT_CYCLE_AXIOM = 'fof(input_cycle_%s, axiom, ' \
                    '(\n\t![T]: ((succ(T) != T) => ((input(T) = %s) <=> (input(succ(T)) = %s)))\n)).\n'
INPUT_CYCLE_DEFINEDNESS_AXIOM = 'fof(input_cycle_definedness, axiom, (\n\t![T]: (%s)\n)).\n'
PATH_SWITCHED_AXIOM = 'fof(switched_path%d, axiom, (\n\t![T]: (switched(T,path%d) <=> (%s))\n)).\n'
FREE_PATH_AXIOM = 'fof(free_path%d, axiom, (\n\t![T]: (free(T,path%d) <=> (![X]: (%s)))\n)).\n'
SAFE_PATH_AXIOM = 'fof(safe_path%d, axiom, (\n\t![T]: (safe(T,path%d) <=> (free(T,path%d) & %s))\n)).\n'
PATH_AVAILABLE_AXIOM = 'fof(available_path, axiom, (\n\t' \
                       '![T,P]: (available(T,P) <=> (safe(T,P) & switched(T,P)))\n)).\n'
AVAILABLE_RESTRICTION_AXIOM = 'fof(available_restriction_axiom, axiom, (\n\t![T,P]: (available(T,P) => (%s))\n)).\n'
TRAIN_SIGNAL_AXIOM = 'fof(train_signal, axiom, ' \
                     '(\n\t![T,I,O]: (signal(T,I,O) <=> (?[X]: (at(T,X,I) & dest(X) = O)))\n)).\n'
SIGNAL_RESTRICTION_AXIOM = 'fof(signal_restriction, axiom, ' \
                           '(\n\t![T,I,O]: (signal(T,I,O) => (%s))\n)).\n'
PATH_SELECTION_AXIOM = 'fof(selected_path%d, axiom, ' \
                       '(\n\t![T]: (selected(T,path%d) <=> ' \
                       '(signal(T,%s,%s) & available(T,path%d) & input(T) = %s))\n)).\n'
PATH_CONTROL_AXIOM = 'fof(path_control, axiom, ' \
                     '(\n\t![T,P]: (switched(succ(T),P) <=> (selected(T,P) | (switched(T,P) & ~free(T,P))))\n)).\n'
INPUT_CONTROL_AXIOM = 'fof(open_%s, axiom, (\n\t![T]: (open(succ(T),%s) <=> (%s))\n)).\n'
TRAIN_DESTINATION_AXIOM = 'fof(train_destinations, axiom, (\n\t![X]: (%s)\n)).\n'
PATH_EXCLUSIVITY_AXIOM = 'fof(path_exclusivity, axiom, (\n\t%s\n)).\n'
OPEN_RESTRICTION_AXIOM = 'fof(open_restriction, axiom, (\n\t![T,N]: (open(T,N) => (%s))\n)).\n'

# critical states axioms
NO_CRASH_AXIOM = 'fof(no_crash, axiom, (\n\t![T,N]: (nocrash(T,N) <=> (\n\t\t' \
                 '![X,Y]: ((at(T,X,N) & at(T,Y,N)) => (X = Y))\n\t))\n)).\n'
NO_CRASH_RESTRICTION_AXIOM = 'fof(no_crash_restriction, axiom, (\n\t![T,N]: (nocrash(T,N) => (%s))\n)).\n'
NO_DERAIL_AXIOM = 'fof(no_derail, axiom, (\n\t![N]: (noderail(N) <=> (\n\t\t' \
                  '![T,X]: ((at(T,X,N) & at(succ(T),X,N)) => (switch(T,N) = switch(succ(T),N)))\n\t))\n)).\n'
NO_BLOCK_AXIOM = 'fof(no_block, axiom, (\n\t![N]: (noblock(N) <=> (\n\t\t' \
                 '![X,T1]: ((at(T1,X,N) & ~open(T1,N)) => (?[T2]: (less(T1,T2) & open(T2,N))))\n\t))\n)).\n'

# critical state check conjectures
CRASH_CHECK_CONJECTURE = 'fof(check_crash, conjecture, (\n\t![T,N]: nocrash(T,N)\n)).\n'
DERAIL_CHECK_CONJECTURE = 'fof(check_derail, conjecture, (\n\t%s\n)).\n'
OPEN_CHECK_CONJECTURE = 'fof(check_open, conjecture, (\n\t%s\n)).\n'


def include(file, dir_path):
    """Generates include directive for given file in given directory."""
    return "include('%s').\n" % os.path.join(dir_path, file)


def generate_order_axioms(dir_path):
    """Generates order axioms."""
    with open(os.path.join(dir_path, 'order.p'), 'w') as order_file:
        order_file.writelines([ANTISYMMETRY_AXIOM, '\n', TRANSITIVITY_AXIOM, '\n', TOTALITY_AXIOM, '\n',
                               SUCCESSOR_AXIOM, '\n', PREDECESSOR_AXIOM])
        order_file.close()


def generate_station_axioms(graph, inputs, outputs, switches, dir_path):
    """Generates station physics axioms."""
    with open(os.path.join(dir_path, 'station.p'), 'w') as station_file:

        # include order and consistency axioms
        lines = list([include('order.p', dir_path), include('consistency.p', dir_path)])

        # train predicate axiom
        lines += [TRAIN_DOCS, TRAIN_AXIOM]

        # at predicate axioms
        lines += [AT_DOCS]
        lines += [AT_INPUT_AXIOM % (in_node, in_node, in_node, in_node, in_node) for in_node in sorted(inputs)]
        for to_node in sorted(set(graph.nodes()) - inputs):
            axiom_body = ''
            for from_node in graph.predecessors(to_node):
                if from_node in inputs:
                    axiom_body += '(at(T,X,%s) & open(T,%s)) | ' % (from_node, from_node)
                elif from_node in switches:
                    axiom_body += '(at(T,X,%s) & switch(T,%s) = %s) | ' % (from_node, from_node, to_node)
                else:
                    axiom_body += 'at(T,X,%s) | ' % from_node
            lines.append(
                AT_OUTPUT_AXIOM % (to_node, to_node, axiom_body[:-3]) if to_node in outputs else
                AT_OTHER_AXIOM % (to_node, to_node, axiom_body[:-3], to_node))

        # train exit axioms
        lines.append(TRAIN_EXIT_DOCS)
        lines += [TRAIN_EXIT_AXIOM % (out_node, out_node, out_node) for out_node in sorted(outputs)]

        # other axioms
        lines += [AT_UNIQUENESS_DOCS, AT_UNIQUENESS_AXIOM,
                  TRAIN_UNIQUENESS_DOCS, TRAIN_UNIQUENESS_AXIOM,
                  ENTER_SAFETY_DOCS, ENTER_SAFETY_AXIOM,
                  ENTER_UNIQUENESS_DOCS, ENTER_UNIQUENESS_AXIOM]

        # at predicate restriction
        axiom_body = ''.join(['(N = %s) | ' % node for node in sorted(graph.nodes())])[:-3]
        lines += [AT_RESTRICTION_DOCS, AT_RESTRICTION_AXIOM % axiom_body]

        # node exclusivity axiom
        axiom_body = ''.join(['(%s != %s) & ' % (u, v) for u, v in combinations(sorted(graph.nodes()), 2)])[:-3]
        lines += [NODE_EXCLUSIVITY_DOCS, NODE_EXCLUSIVITY_AXIOM % axiom_body]

        station_file.writelines(lines)
        station_file.close()


def generate_consistency_axioms(inputs, dir_path):
    """Generates consistency axioms."""
    with open(os.path.join(dir_path, 'consistency.p'), 'w') as consistency_file:

        lines = [GO_IF_POSSIBLE_DOCS, GO_IF_POSSIBLE_AXIOM, ENTER_GENERATOR_DOCS]
        lines += [ENTER_GENERATOR_AXIOM % (in_node, in_node) for in_node in sorted(inputs)]

        consistency_file.writelines(lines)
        consistency_file.close()


def input_cycle(inputs):
    shifted = deque(inputs)
    shifted.rotate(-1)
    return zip(inputs, shifted)


def pairwise(iterable):
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)


def generate_system_axioms(inputs, outputs, switches, paths, dir_path):
    """Generates control system axioms."""
    with open(os.path.join(dir_path, 'system.p'), 'w') as system_file:

        # include station physics axioms
        lines = list(include('station.p', dir_path))

        if len(inputs) > 1:

            # input cycling axioms
            lines.append(INPUT_CYCLE_DOCS)
            lines += [INPUT_CYCLE_AXIOM % (current_input, current_input, next_input)
                      for current_input, next_input in input_cycle(sorted(inputs))]

            # input cycling definedness axiom
            axiom_body = ''.join(['(input(T) = %s) | ' % in_node for in_node in inputs])[:-3]
            lines += [INPUT_CYCLE_DEFINEDNESS_DOCS, INPUT_CYCLE_DEFINEDNESS_AXIOM % axiom_body]

        # switch configuration axioms
        lines.append(PATH_SWITCHED_DOCS)
        for i, path in enumerate(paths):
            axiom_body = ''.join(['(switch(T,%s) = %s) & ' % (switch, node)
                                  for switch, node in pairwise(path) if switch in switches])[:-3] \
                if set(path) & switches else '$true'
            lines.append(PATH_SWITCHED_AXIOM % (i, i, axiom_body))

        # free path axioms
        lines.append(FREE_PATH_DOCS)
        for i, path in enumerate(paths):
            axiom_body = ''.join(['(~at(T,X,%s)) & ' % node for node in path if node not in inputs | outputs])[:-3]
            lines.append(FREE_PATH_AXIOM % (i, i, axiom_body))

        # safe path axioms
        conflict = lambda path1, path2: set(path1) & set(path2) - inputs
        lines.append(SAFE_PATH_DOCS)
        for i, path in enumerate(paths):
            axiom_body = ''.join(['free(T,path%d) & ' % j
                                  for j, p in enumerate(paths) if i != j and conflict(path, p)])[:-3]
            lines.append(SAFE_PATH_AXIOM % (i, i, i, axiom_body))

        # path availability axioms
        lines += [PATH_AVAILABLE_DOCS, PATH_AVAILABLE_AXIOM]

        # available predicate restriction
        axiom_body = ''.join(['(P = path%d) | ' % i for i in range(0, len(paths))])[:-3]
        lines += [AVAILABLE_RESTRICTION_DOCS, AVAILABLE_RESTRICTION_AXIOM % axiom_body]

        # train driver signal axioms
        lines += [TRAIN_SIGNAL_DOCS, TRAIN_SIGNAL_AXIOM]

        # signal restriction axiom
        axiom_body = ''.join('(I = %s & O = %s) | ' % (in_node, out_node)
                             for in_node, out_node in product(sorted(inputs), sorted(outputs)))[:-3]
        lines += [SIGNAL_RESTRICTION_DOCS, SIGNAL_RESTRICTION_AXIOM % axiom_body]

        # path selection axioms
        lines.append(PATH_SELECTION_DOCS)
        lines += [PATH_SELECTION_AXIOM % (i, i, path[0], path[len(path)-1], i, path[0]) for i, path in enumerate(paths)]

        # path control axiom
        lines += [PATH_CONTROL_DOCS, PATH_CONTROL_AXIOM]

        # input control axiom
        lines.append(INPUT_CONTROL_DOCS)
        for in_node in sorted(inputs):
            axiom_body = ''.join(['selected(T,path%d) | ' % i
                                  for i, path in enumerate(paths) if path[0] == in_node])[:-3]
            lines.append(INPUT_CONTROL_AXIOM % (in_node, in_node, axiom_body))

        # train destination axiom
        axiom_body = ''.join('(dest(X) = %s) | ' % out_node for out_node in sorted(outputs))[:-3]
        lines += [TRAIN_DESTINATION_DOCS, TRAIN_DESTINATION_AXIOM % axiom_body]

        # path exclusivity axiom
        axiom_body = ''.join(['(path%d != path%d) & ' % (i, j) for i, j in combinations(range(0, len(paths)), 2)])[:-3]
        lines += [PATH_EXCLUSIVITY_DOCS, PATH_EXCLUSIVITY_AXIOM % axiom_body]

        # open predicate restriction
        axiom_body = ''.join(['(N = %s) | ' % in_node for in_node in sorted(inputs)])[:-3]
        lines += [OPEN_RESTRICTION_DOCS, OPEN_RESTRICTION_AXIOM % axiom_body]

        system_file.writelines(lines)
        system_file.close()


def generate_critical_state_checks(graph, inputs, switches, dir_path):
    """Generates critical states check conjectures."""
    # check that there ain't two trains at one location at the same time
    with open(os.path.join(dir_path, 'check_crash.p'), 'w') as file:
        axiom_body = ''.join(['(N = %s) | ' % in_node for in_node in sorted(graph.nodes())])[:-3]
        file.writelines([include('system.p', dir_path),
                         NO_CRASH_DOCS, NO_CRASH_AXIOM,
                         NO_CRASH_RESTRICTION_DOCS, NO_CRASH_RESTRICTION_AXIOM % axiom_body,
                         CRASH_CHECK_DOCS, CRASH_CHECK_CONJECTURE])
        file.close()

    # check that no train will derail on changing switch (excluding input gates)
    with open(os.path.join(dir_path, 'check_derail.p'), 'w') as file:
        axiom_body = ''.join(['noderail(%s) & ' % switch for switch in sorted(switches)])[:-3]
        file.writelines([include('system.p', dir_path),
                         NO_DERAIL_DOCS, NO_DERAIL_AXIOM,
                         DERAIL_CHECK_DOCS, DERAIL_CHECK_CONJECTURE % axiom_body])
        file.close()

    # check that gates open properly
    with open(os.path.join(dir_path, 'check_open.p'), 'w') as file:
        axiom_body = ''.join(['noblock(%s) & ' % in_node for in_node in sorted(inputs)])[:-3]
        file.writelines([include('system.p', dir_path),
                         NO_BLOCK_DOCS, NO_BLOCK_AXIOM,
                         OPEN_CHECK_DOCS, OPEN_CHECK_CONJECTURE % axiom_body])
        file.close()


def print_graph(inputs, outputs, switches, paths):
    print('inputs:', inputs)
    print('outputs:', outputs)
    print('switches:', switches)
    for i, path in enumerate(paths):
        print('path%d: %s' % (i, path))


def draw_graph(graph, dir_path):
    """Draw given graph in the given directory once as 'graph.eps' and once as 'graph.png' using a 'dot' layout."""
    a_graph = nx.to_agraph(graph)
    a_graph.layout(prog='dot')
    a_graph.draw(os.path.join(dir_path, 'graph.png'))


def partition_nodes(graph):
    """Generate sets of input, output and switch nodes in given graph."""
    inputs = [node for node, in_deg in graph.in_degree_iter() if in_deg == 0]
    outputs = [node for node, out_deg in graph.out_degree_iter() if out_deg == 0]
    switches = [node for node, out_deg in graph.out_degree_iter() if out_deg > 1]
    return set(sorted(inputs)), set(sorted(outputs)), set(sorted(switches))


def in_out_paths_iterator(graph, inputs, outputs):
    path_generators = [nx.all_simple_paths(graph, in_node, out_node)
                       for in_node, out_node in product(sorted(inputs), sorted(outputs))]
    for path_generator in chain(path_generators):
        path_list = list(path_generator)
        while path_list:
            yield path_list.pop()


def in_out_paths(graph, inputs, outputs):
    return [[node for node in path] for path in in_out_paths_iterator(graph, inputs, outputs)]


def formalize(dir_path):
    """Formalizes physics and control system for railway station described by a graph in given directory."""
    print('>>> reading input graph..')
    graph = nx.DiGraph(nx.read_dot(os.path.join(dir_path, 'graph.dot')))
    inputs, outputs, switches = partition_nodes(graph)
    paths = in_out_paths(graph, inputs, outputs)
    print_graph(inputs, outputs, switches, paths)

    print('>>> plotting graph..')
    draw_graph(graph, dir_path)

    print('>>> formalizing..')
    generate_order_axioms(dir_path)
    generate_station_axioms(graph, inputs, outputs, switches, dir_path)
    generate_consistency_axioms(inputs, dir_path)
    generate_system_axioms(inputs, outputs, switches, paths, dir_path)
    generate_critical_state_checks(graph, inputs, switches, dir_path)


def find(file_path, sat):
    with open(file_path, 'r') as file:
        for line in file:
            if sat(line):
                file.close()
                return True
        file.close()
    return False


def prove_system_correctness(dir_path):

    print('>>> proving system correctness..')

    model = lambda file_path: find(file_path, lambda line: 'Exiting with' in line and 'model.' in line)
    proof = lambda file_path: find(file_path, lambda line: 'THEOREM PROVED' in line)

    # find model for the station physics
    in_path, out_path = os.path.join(dir_path, 'station.p'), os.path.join(dir_path, 'station.out')
    call('cat %s | tptp_to_ladr | mace4 > %s 2> /dev/null' % (in_path, out_path), shell=True)
    result = ' OK' if model(out_path) else ' NO'
    print('station physics ' + '.' * 21 + result)

    # find model for the control system
    in_path, out_path = os.path.join(dir_path, 'system.p'), os.path.join(dir_path, 'system.out')
    call('cat %s | tptp_to_ladr | mace4 > %s 2> /dev/null' % (in_path, out_path), shell=True)
    result = ' OK' if model(out_path) else ' NO'
    print('system control ' + '.' * 22 + result)

    # critical states check
    check_files = sorted([f for f in os.listdir(dir_path)
                          if os.path.isfile(os.path.join(dir_path, f)) and f.startswith('check') and f.endswith('.p')])

    for check_file in check_files:
        in_path, out_path = os.path.join(dir_path, check_file), os.path.join(dir_path, check_file.replace('.p', '.out'))
        call('cat %s | tptp_to_ladr | prover9 > %s 2> /dev/null' % (in_path, out_path), shell=True)
        check_type = check_file.replace('.p', '').replace('_', ' ')
        result = ' OK' if proof(out_path) else ' NO'
        print('%s ' % check_type + '.' * (36 - len(check_type)) + result)


def usage():
    """Prints usage for this script on the standard output."""
    print('Usage:')
    print('\t$ python3 sysgen.py [-h | --help | -p | --proof] <system_dir>')
    print('\nExample:')
    print('\t$ python3 sysgen.py --proof examples/ex1')
    print('\nArguments:')
    print("\t<system_dir>\tinput/output directory (must contain file 'graph.dot')")
    print('\nOptions:')
    print('\t-h (--help)\tdisplays usage')
    print("\t-p (--proof)\tadditionally tries to prove system correctness (calls 'mace4' and 'prover9')")
    print('\nRequirements:')
    print("\t'networkx'\thttp://networkx.github.io")


def main():
    """Main method of the script."""
    try:
        opts, args = getopt.getopt(sys.argv[1:], 'hp', ['help', 'prove'])
        if not args:
            usage()
            sys.exit(1)
    except getopt.GetoptError as err:
        print(str(err))
        usage()
        sys.exit(1)
    for opt, arg in opts:
        if opt in ('-h', '--help'):
            usage()
            sys.exit()
        elif opt in ('-p', '--prove'):
            dir_path = args[0]
            if os.path.isdir(dir_path) and 'graph.dot' in os.listdir(dir_path):
                formalize(dir_path)
                prove_system_correctness(dir_path)
                sys.exit()
        else:
            usage()
            sys.exit(1)

    dir_path = args[0]
    if os.path.isdir(dir_path) and 'graph.dot' in os.listdir(dir_path):
        formalize(dir_path)

if __name__ == '__main__':
    main()
