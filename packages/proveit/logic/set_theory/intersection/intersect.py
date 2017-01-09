from proveit import Literal, AssociativeOperation, USE_DEFAULTS
from proveit.logic import InSet, TRUE, FALSE
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
    
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in (A intersection B)], derive and return [(element in A) and (element in B)],
        where self represents (A intersection B). 
        '''
        from _axioms_ import intersectionUnfolding
        return intersectionUnfolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From  [(element in A) and (element in B)], derive and return [element in (A intersection B)],
        where self represents (A intersection B). 
        '''
        from _axioms_ import intersectionFolding
        return intersectionFolding.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def evaluateMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate [element in (A intesection B)] to be TRUE or FALSE, dependent on whether or
        not [(element in A) and (element in B)].
        '''
        from _axioms_ import intersectionEvalTrue, intersectionEvalViaNotInLeft, intersectionEvalViaNotInRight
        inAevaluation = InSet(element, self.operands[0]).evaluate(assumptions=assumptions).rhs
        inBevaluation = InSet(element, self.operands[1]).evaluate(assumptions=assumptions).rhs
        if inAevaluation==TRUE and inBevaluation==TRUE:
            return intersectionEvalTrue.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        elif inAevaluation==FALSE:
            return intersectionEvalViaNotInLeft.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
        else:
            return intersectionEvalViaNotInRight.specialize({x:element, A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
