from proveit import defaults, Function, Literal, USE_DEFAULTS
from proveit.number.sets import Integers, Naturals

class Round(Function):
    # operator of the Round operation.
    _operator_ = Literal(stringFormat='round', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Round._operator_, A)
        # self.operand = A # check later that the operand attribute
        # is still working!

    def _closureTheorem(self, numberSet):
        from . import _theorems_
        if numberSet == Naturals:
            return _theorems_.roundRealPosClosure
        elif numberSet == Integers:
            return _theorems_.roundRealClosure

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        Created: 3/28/2020 by wdc.
        Last modified: 3/28/2020 by wdc. Creation. Based on roughly
                       analogous methods in Add and Exp classes. May
                       need to be renamed.

        For the trivial case where the operand is an integer,
        derive and return this Round expression equated with the
        operand itself. Assumptions may be necessary to deduce
        necessary conditions for the simplification.
        '''
        from proveit._common_ import x
        from ._theorems_ import roundOfInteger
        return roundOfInteger.specialize(
                {x:self.operand}, assumptions=assumptions)

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        expression is in that number set using the appropriate closure
        theorem.
        Created: 3/28/2020 by wdc, based on similar methods in Add, Exp,
                 etc., classes.
        Last Modified: 3/28/2020 by wdc. Creation.
        Once established, these authorship notations can be deleted.
        '''
        from proveit._common_ import x
        from proveit.logic import InSet
        from proveit.number.rounding._theorems_ import (
                  roundRealClosure, roundRealPosClosure)

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Integers:
            return roundRealClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        if number_set == Naturals:
            return roundRealPosClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        msg = ("'Floor.deduceInNumberSet()' not implemented for the "
               "%s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)
            
