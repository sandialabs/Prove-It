from proveit import Literal, BinaryOperation
from proveit.common import x, S

NOTIN = Literal(__package__, stringFormat = 'not in', latexFormat = r'\notin')

class NotInSet(BinaryOperation):
    def __init__(self, element, domain):
        BinaryOperation.__init__(self, NOTIN, element, domain)
        self.element = element
        self.domain = domain  

    @classmethod
    def operatorOfOperation(subClass):
        return NOTIN    
    
    def deduceInBool(self):
        '''
        Deduce and return that this 'not in' statement is in the set of BOOLEANS.
        '''
        self.domain.deduceNotInSetIsBool(self.element)
    
    def unfold(self):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        from theorems import unfoldNotIn
        return unfoldNotIn.specialize({x:self.element, S:self.domain}).deriveConclusion().checked({self})

