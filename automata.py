"""
from 'Damn Cool Algorithms' blog
http://blog.notdot.net/2010/07/Damn-Cool-Algorithms-Levenshtein-Automata
"""

import bisect
import itertools
import time
from collections import defaultdict
from typing import Dict
from typing import FrozenSet
from typing import Optional
from typing import Set
from typing import Tuple

State = Tuple[int, int]  # tuple of (position, distance)
DFAState = FrozenSet[State]  # a set of all NFA states reachable with the same input


class NFA(object):
    """
    non-deterministic finite state automaton
    from some state, given a transition (ie. a character), can end up at multiple states

    state is a tuple of (current_char_index, current_edit_distance)
    """

    # special transition types
    EPSILON: str = object()  # a transition that happens "for free" with no input, basically re.compile(r'')
    ANY: str = object()  # a transition that happens "by default" with any input, basically re.compile(r'.')

    def __init__(self):
        self.transitions: Dict[State, Dict[str, Set[State]]] = dict()
        self.final_states: Set[State] = set()

    @property
    def start_dfa_state(self) -> DFAState:
        """
        the (frozen) set of all states that are epsilon away from (0, 0)
        """
        return self._expand_epsilon({(0, 0)})

    def add_transition(self,
                       src: State,
                       input_char: str,
                       dest: State,
                       ):
        self.transitions.setdefault(src, dict()).setdefault(input_char, set()).add(dest)

    def add_final_state(self, state: State):
        self.final_states.add(state)

    def is_final_dfa_state(self, dfa_state: DFAState) -> bool:
        return not self.final_states.isdisjoint(dfa_state)

    def _expand_epsilon(self, states: Set[State]) -> DFAState:
        """
        expands a set of states in-place to include states that are any number of epsilon transitions away
        """

        frontier = set(states)  # make a copy for the frontier
        while frontier:
            state = frontier.pop()
            new_states = self.transitions.get(state, dict()).get(NFA.EPSILON, set()).difference(states)
            frontier.update(new_states)
            states.update(new_states)
        return frozenset(states)

    def next_dfa_state(self,
                       dfa_state: DFAState,
                       input_char: str,
                       ) -> DFAState:
        dest_states = set()
        for state in dfa_state:
            state_transitions = self.transitions.get(state, dict())
            dest_states.update(state_transitions.get(input_char, set()))
            dest_states.update(state_transitions.get(NFA.ANY, set()))
        return self._expand_epsilon(dest_states)

    def get_inputs(self, dfa_state: DFAState) -> Set[str]:
        """
        outgoing transitions
        """

        inputs = set()
        for state in dfa_state:
            inputs.update(self.transitions.get(state, dict()).keys())
        return inputs

    def to_dfa(self) -> 'DFA':
        """
        create a dfa from this nfa

        each dfa state is the (frozen) set of all states reachable by a specific input
        instead of using the state directly, it's converted to a unique integer to save space

        but since we only use this dfa once and then discard it, there isn't much point to space optimization
        especially since we still need all frozen sets in-memory when building the dfa
        so the max memory usage might not have changed much
        """
        dfa_node_ids: Dict[DFAState, int] = defaultdict(itertools.count().__next__)
        dfa = DFA(dfa_node_ids[self.start_dfa_state])

        frontier = [self.start_dfa_state]
        while frontier:
            current_state = frontier.pop()

            for input_char in self.get_inputs(current_state).difference({NFA.EPSILON}):

                next_state = self.next_dfa_state(current_state, input_char)
                if next_state not in dfa_node_ids:
                    frontier.append(next_state)
                    if self.is_final_dfa_state(next_state):
                        dfa.add_final_state(dfa_node_ids[next_state])

                if input_char == NFA.ANY:
                    dfa.set_default_transition(dfa_node_ids[current_state], dfa_node_ids[next_state])
                else:
                    dfa.add_transition(dfa_node_ids[current_state], input_char, dfa_node_ids[next_state])

        return dfa


class DFA(object):
    """
    deterministic finite state automaton
    from some state, given a transition, goes to a single next state
    """

    def __init__(self,
                 start_state: int,
                 ):
        self.start_state: int = start_state
        self.transitions: Dict[int, Dict[str, int]] = dict()
        self.defaults: Dict[int, int] = dict()
        self.final_states: Set[int] = set()

    def add_transition(self,
                       src: int,
                       input_char: str,
                       dest: int,
                       ):
        self.transitions.setdefault(src, dict())[input_char] = dest

    def set_default_transition(self,
                               src: int,
                               dest: int,
                               ):
        self.defaults[src] = dest

    def add_final_state(self,
                        state: int,
                        ):
        self.final_states.add(state)

    def is_final(self,
                 state: Optional[int],
                 ) -> bool:
        return state in self.final_states

    def next_state(self,
                   src: int,
                   input_char: str,
                   ) -> Optional[int]:
        state_transitions = self.transitions.get(src, dict())
        return state_transitions.get(input_char, self.defaults.get(src, None))

    def next_valid_string(self,
                          input_str: str,
                          ) -> Optional[str]:
        stack = []

        # Evaluate the DFA as far as possible
        state = self.start_state
        char_idx = -1
        for char_idx, input_char in enumerate(input_str):
            stack.append((input_str[:char_idx], state, input_char))
            state = self.next_state(state, input_char)
            if not state:
                break
        else:
            stack.append((input_str[:char_idx + 1], state, None))

        # Input word is already valid?
        if self.is_final(state):
            return input_str

        # Perform a 'wall following' search for the lexicographically smallest accepting state.
        while stack:
            path, state, char = stack.pop()
            char = self.find_next_edge(state, char)
            if char is not None:
                path += char
                state = self.next_state(state, char)
                if self.is_final(state):
                    return path
                stack.append((path, state, None))
        return None

    def find_next_edge(self, state, transition):
        next_allowed_transition = u'\0' if transition is None else chr(ord(transition) + 1)
        state_transitions = self.transitions.get(state, dict())
        if next_allowed_transition in state_transitions or state in self.defaults:
            return next_allowed_transition

        labels = [label for label in state_transitions.keys() if label >= next_allowed_transition]
        if labels:
            return min(labels)
        return None


def levenshtein_automaton(word, k):
    nfa = NFA()
    for index, char in enumerate(word):
        for dist in range(k + 1):
            # Correct character
            nfa.add_transition((index, dist), char, (index + 1, dist))  # edit here to make it case insensitive
            if dist < k:
                # Deletion
                nfa.add_transition((index, dist), NFA.ANY, (index, dist + 1))
                # Insertion
                nfa.add_transition((index, dist), NFA.EPSILON, (index + 1, dist + 1))
                # Substitution
                nfa.add_transition((index, dist), NFA.ANY, (index + 1, dist + 1))
    for dist in range(k + 1):
        if dist < k:
            nfa.add_transition((len(word), dist), NFA.ANY, (len(word), dist + 1))
        nfa.add_final_state((len(word), dist))
    return nfa


def find_all_matches(word, k, lookup_func):
    """Uses lookup_func to find all words within levenshtein distance k of word.

    Args:
      word: The word to look up
      k: Maximum edit distance
      lookup_func: A single argument function that returns the first word in the
        database that is greater than or equal to the input argument.
    Yields:
      Every matching word within levenshtein distance k from the database.
    """
    lev = levenshtein_automaton(word, k).to_dfa()
    match = lev.next_valid_string(u'\0')  # this is such a hack, todo: fix
    while match:
        next_word = lookup_func(match)
        if not next_word:
            return
        if match == next_word:
            yield match
            next_word += u'\0'
        match = lev.next_valid_string(next_word)


def intersect(dfa1, dfa2):
    """
    unused code
    """
    stack = [('', dfa1.start_dfa_state, dfa2.start_dfa_state)]
    while stack:
        s, state1, state2 = stack.pop()
        for edge in set(dfa1.edges(state1)).intersection(dfa2.edges(state2)):
            state1 = dfa1.next(state1, edge)
            state2 = dfa2.next(state2, edge)
            if state1 and state2:
                s = s + edge
                stack.append((s, state1, state2))
                if dfa1.is_final_dfa_state(state1) and dfa2.is_final_dfa_state(state2):
                    yield s


class Matcher(object):
    def __init__(self, entries):
        # self.sorted_entries = sorted(entries)  # re-sorting a list is O(1) after all
        self.sorted_entries = entries
        self.probes = 0
        self.prev = 0

    def __call__(self, word):
        self.probes += 1
        pos = bisect.bisect_left(self.sorted_entries, word, lo=self.prev)
        self.prev = pos
        if pos < len(self.sorted_entries):
            return self.sorted_entries[pos]
        else:
            return None


def levenshtein(s1, s2):
    if len(s1) < len(s2):
        return levenshtein(s2, s1)
    if not s1:
        return len(s2)

    previous_row = range(len(s2) + 1)
    for idx_1, char_1 in enumerate(s1):
        current_row = [idx_1 + 1]
        for idx_2, char_2 in enumerate(s2):
            insertions = previous_row[idx_2 + 1] + 1
            # j+1 instead of j since previous_row and current_row are one character longer than s2
            deletions = current_row[idx_2] + 1
            substitutions = previous_row[idx_2] + (char_1 != char_2)
            current_row.append(min(insertions, deletions, substitutions))
        previous_row = current_row

    return previous_row[-1]


if __name__ == '__main__':

    t = time.time()
    words = sorted(line.split(',')[0].strip().lower() for line in open('english_wikipedia.txt', encoding='utf8'))
    print(len(words), 'total words sorted and loaded')
    print('seconds:', time.time() - t)

    while True:
        query_str = input('Word to find: ')
        if not query_str:
            break
        x = int(input('Edit distance (positive integer): '))

        print('lev automaton')
        t = time.time()
        m = Matcher(words)
        found = list(find_all_matches(query_str, x, m))
        print('seconds:', time.time() - t)
        print('probes:', m.probes, '=', float(m.probes) / len(words))
        print('found:', len(found), found[:25])
