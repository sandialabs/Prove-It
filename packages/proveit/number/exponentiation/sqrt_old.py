## Until Thurs 2/27/2020, we utilized the Sqrt class from this sqrt.py
## Replaced Sqrt class with a special sqrt() function that produces
## a special version of an Exp expression, and that sqrt() function
## can now be found in exp.py (defined outside any specific class).

from proveit import Literal, Operation, USE_DEFAULTS

class Sqrt(Operation):
    # operator of the Exp operation.
    _operator_ = Literal(stringFormat='sqrt', context=__file__)    
    
    def __init__(self, base):
        r'''
        Take the square root of the base.
        '''
        Operation.__init__(self, Sqrt._operator_, base)
        self.base = base
                    
    def latex(self, **kwargs):
        return r'\sqrt{' + self.base.latex()+'}'
    
    def distribute(self):
        '''
        Distribute the sqrt over a product.
        '''
        from proveit.number import Mult
        from .theorems import sqrtOfProd
        if isinstance(self.base, Mult):
            deduceInRealsPos(self.base.factors)
            return sqrtOfProd({xEtc:self.base.factors})

    def _closureTheorem(self, numberSet):
        from . import theorems
        from proveit.number import two
        if numberSet == Reals:
            return theorems.sqrtRealClosure            
        elif numberSet == RealsPos:
            return theorems.sqrtRealPosClosure            
        elif numberSet == Complexes:
            return theorems.sqrtComplexClosure

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem.
        Created: 2/23/2020 by wdc, based on the same method in the Add
                 class.
        Last Modified: 2/23/2020 by wdc. Creation.
        Once established, these authorship notations can be deleted.
        '''
        
        from proveit._common_ import a
        from proveit.logic import InSet
        from proveit.number.exponentiation._theorems_ import (
                  sqrtRealClosure, sqrtRealPosClosure, sqrtComplexClosure)
        from proveit.number import Complexes, Reals, RealsPos

        if number_set == Reals:
            return sqrtRealClosure.specialize({a:self.base},
                      assumptions=assumptions)

        if number_set == RealsPos:
            return sqrtRealPosClosure.specialize({a:self.base},
                      assumptions=assumptions)

        if number_set == Complexes:
            return sqrtComplexClosure.specialize({a:self.base},
                      assumptions=assumptions)
