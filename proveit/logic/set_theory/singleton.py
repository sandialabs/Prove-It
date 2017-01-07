from proveit import Literal, Operation, USE_DEFAULTS
from proveit.common import x, y

SINGLETON = Literal(__package__, stringFormat = 'SINGLETON')

class Singleton(Operation):
    '''
    Defines a set with only one item.
    '''
    def __init__(self, elem):
        Operation.__init__(self, SINGLETON, elem)
        self.elem = elem

    @classmethod
    def operatorOfOperation(subClass):
        return SINGLETON    

    def string(self, **kwargs):
        return '{' + str(self.elem) + '}'
    
    def latex(self, **kwargs):
        return r'\{' + self.elem.latex() + r'\}'        
 
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in {y}], derive and return (element = y).
        '''
        from _axioms_ import singletonDef
        return singletonDef.specialize({x:element, y:self.elem}).deriveRightViaEquivalence(assumptions=assumptions)
    
    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From (element = y), derive and return [element in {y}] where self represents {y}.
        '''   
        from _axioms_ import singletonDef
        return singletonDef.specialize({x:element, y:self.elem}).deriveLeftViaEquivalence(assumptions=assumptions)

    def evaluateMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        Attempt to evaluate [element in {y}] to be TRUE or FALSE, dependent on whether or
        not element=y.
        '''
        from proveit.logic import Equals, TRUE, FALSE 
        from _theorems_ import inSingletonEvalTrue, inSingletonEvalFalse
        # determine whether the membership evaluates to TRUE or FALSE
        evaluation = Equals(element, self.elem).evaluate(assumptions).rhs
        if evaluation == TRUE:
            # short proof that it evaluates to TRUE
            return inSingletonEvalTrue.specialize({x:element, y:self.elem})
        elif evaluation == FALSE:
            # short proof that it evaluates to FALSE
            return inSingletonEvalFalse.specialize({x:element, y:self.elem})
        
        