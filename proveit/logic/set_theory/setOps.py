from proveit import BinaryOperation, AssociativeOperation, OperationOverInstances
from proveit import Operation, Literal, Etcetera, MultiVariable, USE_DEFAULTS
from proveit.common import f, x, y, A, B, S, P, Q, yEtc


pkg = __package__

COMPLEMENT = Literal(pkg, stringFormat = 'COMPLEMENT')




class Complement(Operation):        
    '''
    The complement of a set is everything outside that set.
    '''
    def __init__(self, elem):
        Operation.__init__(self, COMPLEMENT, elem)
        self.elem = elem

    @classmethod
    def operatorOfOperation(subClass):
        return COMPLEMENT    



 


