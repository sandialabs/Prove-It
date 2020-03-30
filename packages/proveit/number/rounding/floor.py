from proveit import defaults, Literal, Function, USE_DEFAULTS
from proveit.number.sets import Integers, Naturals

class Floor(Function):
    # operator of the Floor operation.
    _operator_ = Literal(stringFormat='floor', context=__file__)
    
    def __init__(self, A):
        Function.__init__(self, Floor._operator_, A)
        # self.operand = A # check later that the operand attribute
        # is still working!

    def _closureTheorem(self, numberSet):
        from . import _theorems_
        if numberSet == Naturals:
            return _theorems_.floorRealPosClosure
        elif numberSet == Integers:
            return _theorems_.floorRealClosure
            
    def latex(self, **kwargs):
        return r'\lfloor ' + self.operand.latex(fence=False) + r'\rfloor'

    # def doReducedSimplification(self, assumptions=USE_DEFAULTS):
    #     '''
    #     Created: 3/28/2020 by wdc.
    #     Last modified: 3/28/2020 by wdc. Creation. Based on roughly
    #                    analogous methods in Add and Exp classes. May
    #                    need to be renamed.

    #     For the trivial case where the operand is an integer,
    #     derive and return this Floor expression equated with the
    #     operand itself. Assumptions may be necessary to deduce
    #     necessary conditions for the simplification.
    #     '''
    #     from proveit._common_ import x
    #     from ._theorems_ import floorOfInteger
    #     return floorOfInteger.specialize(
    #             {x:self.operand}, assumptions=assumptions)

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        Created: 3/30/2020 by wdc.
        Last modified: 3/30/2020 by wdc. Creation. Based on roughly
                       analogous methods in Add and Exp classes. May
                       need to be renamed.

        For the trivial case where the operand is an integer,
        derive and return this Round expression equated with the
        operand itself. Assumptions may be necessary to deduce
        necessary conditions for the simplification.
        For the case where the operand is of the form (real + int),
        derive and return this Round expression equated with
        Round(real) + int.
        CONSIDER ADDING A RECURSIVE COMPONENT to allow further 
        simplfication, for example for Round(real + int + int).
        '''
        from proveit._common_ import n, x
        from proveit.number import Add, Integers
        from ._theorems_ import floorOfInteger, floorOfRealPlusInt
        try:
            return floorOfInteger.specialize(
                    {x:self.operand}, assumptions=assumptions)
        except:
            if isinstance(self.operand, Add):
                subops = self.operand.operands
                if len(subops)==2:
                    xsub = subops[0]
                    nsub = subops[1]
                else:
                    xsub = Add(subops[:-1])
                    n: subops[-1]
                return floorOfRealPlusInt.specialize(
                        {x:xsub, n:nsub}, assumptions=assumptions)
            else:
                raise ValueError("Floor.doReducedSimplification() method "
                                 "expecting simpler operands. Consider "
                                 "reviewing the floorOfInteger and "
                                 "floorOfRealPlusInt theorems in the "
                                 "proveit/number/rounding context.")
        
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
                  floorRealClosure, floorRealPosClosure)

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Integers:
            return floorRealClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        if number_set == Naturals:
            return floorRealPosClosure.specialize({x:self.operand},
                      assumptions=assumptions)

        msg = ("'Floor.deduceInNumberSet()' not implemented for the "
               "%s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)
