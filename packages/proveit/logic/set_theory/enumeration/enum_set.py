from proveit import Literal, Operation, ExprList, USE_DEFAULTS
from proveit._common_ import x, y, yMulti

class Set(Operation):
    '''
    Defines a set with only one item.
    '''
    
    # operator of the Set operation
    _operator_ = Literal(stringFormat='Set', context=__file__) 
    
    def __init__(self, *elems):
        Operation.__init__(self, Set._operator_, elems)
        self.elements = self.operands

    def string(self, **kwargs):
        return '{' + ExprList(self.elements).string(fence=False) + '}'
    
    def latex(self, **kwargs):
        return r'\left\{' + ExprList(self.elements).latex(fence=False) + r'\right\}'        

    def membershipEquivalence(self, element, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element in {x, y, ..}] = [(element=x) or (element=y) or ...] 
        where self = {y}.
        '''
        from _axioms_ import enumSetDef
        from _theorems_ import singletonDef
        if len(self.elements) == 1:
            return singletonDef.specialize({x:element, y:self.elements[0]})
        else:
            return enumSetDef.specialize({x:element, yMulti:self.elements})

    def nonmembershipEquivalence(self, element):
        '''
        Deduce and return and [element not in {x, y, ..}] = [(element != x) and (element != y) and ...]
        where self = {y}.
        '''
        from _theorems_ import notInSingletonEquiv, nonmembershipEquiv
        if len(self.elements) == 1:
            return notInSingletonEquiv.specialize({x:element, y:self.elem})
        else:
            return nonmembershipEquiv.specialize({x:element, yMulti:self.elements})
  
    def unfoldMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [element in {x, y, ..}], derive and return [(element=x) or (element=y) or ..].
        '''
        from _theorems_ import unfoldSingleton, unfold
        if len(self.elements) == 1:
            return unfoldSingleton.specialize({x:element, y:self.elem})
        else:
            return unfold.specialize({x:element, yMulti:self.elements})
            
    def deduceMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From [(element=x) or (element=y) or ..], derive and return [element in {x, y, ..}].
        '''   
        from _theorems_ import foldSingleton, fold
        if len(self.elements) == 1:
            return foldSingleton.specialize({x:element, y:self.elem})
        else:
            return fold.specialize({x:element, yMulti:self.elements})