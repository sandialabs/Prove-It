'''
Socks.py
Wayne Witzel
March 2017

Classes/methods that are useful for solving the "matching socks" problem
that demonstrates theorem proving and axiom elimination in the tutorial.
'''

from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import x, S

'''
The Color operation returns the color of a given sock.
'''


class Color(Operation):
    # operator of the Color operation
    _operator_ = Literal(
        string_format='Color',
        latex_format=r'{\rm Color}',
        theory=__file__)

    def __init__(self, sock):
        return Operation.__init__(self, Color._operator_, sock)


'''
The MatchingSubset operation returns the subset of a set of socks
that are of a given color.
'''


class MatchingSubset(Operation):
    # operator of the ColoredSubset operation
    _operator_ = Literal(
        string_format='MatchingSubset',
        latex_format=r'{\rm MatchingSubset}',
        theory=__file__)

    def __init__(self, sock_set, color):
        self.sock_set = sock_set
        self.color = color
        return Operation.__init__(
            self, MatchingSubset._operator_, [
                sock_set, color])

    def definition(self):
        '''
        Derive the definition of this MatchingSubset(S, color) in the form of an equation.
        '''
        from ._axioms_ import matching_subset_def
        from _common_ import color
        return matching_subset_def.instantiate(
            {S: self.sock_set, color: self.color})

    def unfold_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [x in MatchingSubset(S, color)], derive and return [(x in S) and Color(x)=color], where x is meant as the given element.
        '''
        from ._theorems_ import unfold_matching_subset
        from _common_ import color
        return unfold_matching_subset.instantiate(
            {S: self.sock_set, color: self.color, x: element}, assumptions=assumptions)


"""
'''
The IsMatchingSet operation acting on a set of socks returns TRUE
iff all of the socks are the same color.
'''
class IsMatchingSet(Operation):
    # operator of the IsMatch operation
    _operator_ = Literal(string_format='IsMatchingSet', latex_format=r'{\rm IsMatchingSet}', theory=__file__)

    def __init__(self, sock_a, sock_b):
        return Operation.__init__(self, IsMatchingSet._operator_, [sock_a, sock_b])

'''
The IsMatchingPair operation acting on a set of socks returns TRUE
iff the set is of size two and the two socks are the same color.
'''
class IsMatchingPair(Operation):
    # operator of the IsMatch operation
    _operator_ = Literal(string_format='IsMatchingPair', latex_format=r'{\rm IsMatchingPair}', theory=__file__)

    def __init__(self, sock_a, sock_b):
        return Operation.__init__(self, IsMatchingPair._operator_, [sock_a, sock_b])
"""

'''
The IsMatch operation acting on a pair of socks
returns TRUE if this is a matching pair.
'''


class IsMatch(Operation):
    # operator of the ContainsMatch operation
    _operator_ = Literal(
        string_format='IsMatch',
        latex_format=r'{\rm IsMatch}',
        theory=__file__)

    def __init__(self, a, b):
        self.a, self.b = a, b
        return Operation.__init__(self, IsMatch._operator_, [a, b])

    def definition(self, assumptions=USE_DEFAULTS):
        '''
        Derive the definition of this IsMatch(a, b) in the form of an equation.
        '''
        from ._axioms_ import is_match_def
        from proveit._common_ import a, b
        return is_match_def.instantiate(
            {a: self.a, b: self.b}, assumptions=assumptions)


'''
The ContainsMatch operation acting on a set of socks
returns TRUE iff there exists a pair of socks that match contained in the set.
'''


class ContainsMatch(Operation):
    # operator of the ContainsMatch operation
    _operator_ = Literal(
        string_format='ContainsMatch',
        latex_format=r'{\rm ContainsMatch}',
        theory=__file__)

    def __init__(self, socks):
        self.socks = socks
        return Operation.__init__(self, ContainsMatch._operator_, [socks])

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Conclude via the definition.
        '''
        return self.definition(assumptions).derive_left(assumptions)

    def definition(self, assumptions=USE_DEFAULTS):
        '''
        Derive the definition of this ContainsMatch(S) in the form of an equation.
        '''
        from ._axioms_ import contains_match_def
        from proveit._common_ import S
        return contains_match_def.instantiate(
            {S: self.socks}, assumptions=assumptions)
