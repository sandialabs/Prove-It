from proveit import Literal, Operation
from proveit.common import xEtc

SQRT = Literal(__package__, 'SQRT')

class Sqrt(Operation):
    def __init__(self, base):
        r'''
        Take the square root of the base.
        '''
        Operation.__init__(self, SQRT, (base))
        self.base = base
        
    @classmethod
    def operatorOfOperation(subClass):
        return SQRT
            
    def latex(self, **kwargs):
        return r'\sqrt{' + self.base.latex()+'}'
    
    def distribute(self):
        '''
        Distribute the sqrt over a product.
        '''
        from proveit.number import Mult
        from theorems import sqrtOfProd
        if isinstance(self.base, Mult):
            deduceInRealsPos(self.base.factors)
            return sqrtOfProd({xEtc:self.base.factors})

    def _closureTheorem(self, numberSet):
        import theorems
        from proveit.number import two
        if numberSet == Reals:
            return theorems.sqrtRealClosure            
        elif numberSet == RealsPos:
            return theorems.sqrtRealPosClosure            
        elif numberSet == Complexes:
            return theorems.sqrtComplexClosure
