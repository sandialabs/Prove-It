'''
Socks.py
Wayne Witzel
March 2017

Classes/methods that are useful for solving the "matching socks" problem
that demonstrates theorem proving and axiom elimination in the tutorial.
'''

from proveit import Literal, Operation

COLOR = Literal(__package__, stringFormat = 'Color', latexFormat = r'{\rm Color}')

'''
The Color operation returns the color of a given sock.
'''
class Color(Operation):
    def __init__(self, sock):
        return Operation.__init__(self, COLOR, sock)
    
    @classmethod
    def operatorOfOperation(subClass):
        return COLOR

IS_MATCH = Literal(__package__, stringFormat = 'IsMatch', latexFormat = r'{\rm IsMatch}')

'''
The IsMatch operation acting on two socks returns TRUE 
iff the socks are different but have the same color.
'''
class IsMatch(Operation):
    def __init__(self, sockA, sockB):
        return Operation.__init__(self, IS_MATCH, [sockA, sockB])

    @classmethod
    def operatorOfOperation(subClass):
        return IS_MATCH

CONTAINS_MATCH = Literal(__package__, stringFormat = 'ContainsMatch', latexFormat = r'{\rm ContainsMatch}')

'''
The ContainsMatch operation acting on a set of socks
returns TRUE iff there exists a pair of socks that match contained in the set.
'''
class ContainsMatch(Operation):
    def __init__(self, socks):
        return Operation.__init__(self, CONTAINS_MATCH, [socks])

    @classmethod
    def operatorOfOperation(subClass):
        return CONTAINS_MATCH
