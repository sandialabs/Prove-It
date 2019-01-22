from proveit import USE_DEFAULTS
from proveit.logic import Membership, Nonmembership
from proveit.number import num
from proveit._common_ import l, x, y, yy

class EnumMembership(Membership):
    '''
    Defines methods that apply to membership in an enumerated set. 
    '''
    
    def __init__(self, element, domain):
        Membership.__init__(self, element)
        self.domain = domain
    
    def sideEffects(self, knownTruth):
        '''
        Unfold the enumerated set membership as a side-effect.
        '''
        yield self.unfold

    def conclude(self, assumptions=USE_DEFAULTS):
        '''
        From [(element=x) or (element=y) or ..], derive and return [element in {x, y, ..}].
        '''   
        from ._theorems_ import foldSingleton, fold
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return foldSingleton.specialize({x:self.element, y:enum_elements})
        else:
            return fold.specialize({l:num(len(enum_elements)), x:self.element, yy:enum_elements})
    
    def equivalence(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return and [element in {x, y, ..}] = [(element=x) or (element=y) or ...] 
        where self = {y}.
        '''
        from ._axioms_ import enumSetDef
        from ._theorems_ import singletonDef
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return singletonDef.specialize({x:self.element, y:enum_elements[0]})
        else:
            return enumSetDef.specialize({l:num(len(enum_elements)), x:self.element, yy:enum_elements})

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From [element in {x, y, ..}], derive and return [(element=x) or (element=y) or ..].
        '''
        from ._theorems_ import unfoldSingleton, unfold
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return unfoldSingleton.specialize({x:self.element, y:enum_elements[0]})
        else:
            return unfold.specialize({l:num(len(enum_elements)), x:self.element, yy:enum_elements})
                        
class EnumNonmembership(Nonmembership):
    '''
    Defines methods that apply to non-membership in an enumerated set. 
    '''
    
    def __init__(self, element, domain):
        Nonmembership.__init__(self, element)
        self.domain = domain

    def equivalence(self):
        '''
        Deduce and return and [element not in {x, y, ..}] = [(element != x) and (element != y) and ...]
        where self = {y}.
        '''
        from ._theorems_ import notInSingletonEquiv, nonmembershipEquiv
        enum_elements = self.domain.elements
        if len(enum_elements) == 1:
            return notInSingletonEquiv.specialize({x:self.element, y:enum_elements})
        else:
            return nonmembershipEquiv.specialize({l:num(len(enum_elements)), x:self.element, yy:enum_elements})
  
            
