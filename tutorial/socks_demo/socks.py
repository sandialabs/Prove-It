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
    _operator_ = Literal(stringFormat='Color', latexFormat=r'{\rm Color}', context=__file__)
    
    def __init__(self, sock):
        return Operation.__init__(self, Color._operator_, sock)

'''
The MatchingSubset operation returns the subset of a set of socks
that are of a given color.
'''
class MatchingSubset(Operation):
    # operator of the ColoredSubset operation
    _operator_ = Literal(stringFormat='MatchingSubset', latexFormat=r'{\rm MatchingSubset}', context=__file__)
    
    def __init__(self, sockSet, color):
        self.sockSet = sockSet
        self.color = color
        return Operation.__init__(self, MatchingSubset._operator_, [sockSet, color])        
        
    def definition(self):
        '''
        Derive the definition of this MatchingSubset(S, color) in the form of an equation.
        '''
        from ._axioms_ import matchingSubsetDef
        from _common_ import color
        return matchingSubsetDef.instantiate({S:self.sockSet, color:self.color})
    
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [x in MatchingSubset(S, color)], derive and return [(x in S) and Color(x)=color], where x is meant as the given element.
        '''
        from ._theorems_ import unfoldMatchingSubset
        from _common_ import color
        return unfoldMatchingSubset.instantiate({S:self.sockSet, color:self.color, x:element}, assumptions=assumptions)        
        

"""
'''
The IsMatchingSet operation acting on a set of socks returns TRUE 
iff all of the socks are the same color.
'''
class IsMatchingSet(Operation):
    # operator of the IsMatch operation
    _operator_ = Literal(stringFormat='IsMatchingSet', latexFormat=r'{\rm IsMatchingSet}', context=__file__)
    
    def __init__(self, sockA, sockB):
        return Operation.__init__(self, IsMatchingSet._operator_, [sockA, sockB])

'''
The IsMatchingPair operation acting on a set of socks returns TRUE 
iff the set is of size two and the two socks are the same color.
'''
class IsMatchingPair(Operation):
    # operator of the IsMatch operation
    _operator_ = Literal(stringFormat='IsMatchingPair', latexFormat=r'{\rm IsMatchingPair}', context=__file__)
    
    def __init__(self, sockA, sockB):
        return Operation.__init__(self, IsMatchingPair._operator_, [sockA, sockB])
"""

'''
The IsMatch operation acting on a pair of socks
returns TRUE if this is a matching pair.
'''
class IsMatch(Operation):
    # operator of the ContainsMatch operation
    _operator_ = Literal(stringFormat='IsMatch', latexFormat=r'{\rm IsMatch}', context=__file__)
    
    def __init__(self, a, b):
        self.a, self.b = a, b
        return Operation.__init__(self, IsMatch._operator_, [a, b])

    def definition(self, assumptions=USE_DEFAULTS):
        '''
        Derive the definition of this IsMatch(a, b) in the form of an equation.
        '''
        from ._axioms_ import isMatchDef
        from proveit._common_ import a, b
        return isMatchDef.instantiate({a:self.a, b:self.b}, assumptions=assumptions)

'''
The ContainsMatch operation acting on a set of socks
returns TRUE iff there exists a pair of socks that match contained in the set.
'''
class ContainsMatch(Operation):
    # operator of the ContainsMatch operation
    _operator_ = Literal(stringFormat='ContainsMatch', latexFormat=r'{\rm ContainsMatch}', context=__file__)
    
    def __init__(self, socks):
        self.socks = socks
        return Operation.__init__(self, ContainsMatch._operator_, [socks])

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        Conclude via the definition.
        '''
        return self.definition(assumptions).deriveLeft(assumptions)
        
    def definition(self, assumptions=USE_DEFAULTS):
        '''
        Derive the definition of this ContainsMatch(S) in the form of an equation.
        '''
        from ._axioms_ import containsMatchDef
        from proveit._common_ import S
        return containsMatchDef.instantiate({S:self.socks}, assumptions=assumptions)
