from proveit import Literal, Operation
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
 
    def unfoldElemInSet(self, element):
        '''
        From [element in {y}], derive and return (element = y).
        '''
        from _axioms_ import singletonDef
        return singletonDef.specialize({x:element, y:self.elem}).deriveRightViaEquivalence()
    
    def deduceElemInSet(self, element):
        '''
        From (element = y), derive and return [element in {y}] where self represents {y}.
        '''   
        from _axioms_ import singletonDef
        return singletonDef.specialize({x:element, y:self.elem}).deriveLeftViaEquivalence()
