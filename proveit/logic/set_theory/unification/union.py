from proveit import Literal, AssociativeOperation
from proveit.common import A, B, x

UNION = Literal(__package__, stringFormat = 'union', latexFormat = r'\bigcup')

        
class Union(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Union any number of sets: A union B union C
        '''
        AssociativeOperation.__init__(self, UNION, *operands)

    @classmethod
    def operatorOfOperation(subClass):
        return UNION    

    def unfoldElemInSet(self, element):
        '''
        From [element in (A union B)], derive and return [(element in A) or (element in B)],
        where self represents (A union B). 
        '''
        from _axioms_ import unionDef
        if len(self.operands) == 2:
            leftOperand, rightOperand = self.operands       
            return unionDef.specialize({x:element, A:leftOperand, B:rightOperand}).deriveRight()

    def deduceElemInSet(self, element):
        '''
        From [(element in A) or (element in B)], derive and return [element in (A union B)]
        where self represents (A union B).
        ''' 
        from _axioms_ import unionDef
        if len(self.operands) == 2:
            leftOperand, rightOperand = self.operands              
            return unionDef.specialize({x:element, A:leftOperand, B:rightOperand}).deriveLeft()

