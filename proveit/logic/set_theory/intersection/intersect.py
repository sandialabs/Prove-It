from proveit import Literal, AssociativeOperation
from proveit.common import x, A, B

INTERSECT = Literal(__package__, stringFormat = 'intersection', latexFormat = r'\cap')

class Intersect(AssociativeOperation):
    def __init__(self, *operands):
        '''
        Intersect any number of set: A intersect B intersect C
        '''
        AssociativeOperation.__init__(self, INTERSECT, *operands)

    @classmethod
    def operatorOfOperation(subClass):
        return INTERSECT  
    
    def unfoldElemInSet(self, element):
        '''
        From [element in (A intersection B)], derive and return [(element in A) and (element in B)],
        where self represents (A intersection B). 
        '''
        from _axioms_ import intersectionDef
        return intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveRight()

    def deduceElemInSet(self, element):
        '''
        From  [(element in A) and (element in B)], derive and return [element in (A intersection B)],
        where self represents (A intersection B). 
        '''
        from _axioms_ import intersectionDef
        return intersectionDef.specialize({x:element, A:self.operands[0], B:self.operands[1]}).deriveLeft()
