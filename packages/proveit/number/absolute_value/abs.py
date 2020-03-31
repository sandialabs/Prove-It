from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit._common_ import a, b, x

class Abs(Operation):
    # operator of the Abs operation.
    _operator_ = Literal(stringFormat='Abs', context=__file__)

    def __init__(self, A):
        Operation.__init__(self, Abs._operator_, A)   
    
    def string(self, **kwargs):
        return '|'+self.operand.string()+'|'

    def latex(self, **kwargs):
        return r'\left|'+self.operand.latex()+r'\right|'

    def notEqual(self, rhs, assumptions=USE_DEFAULTS):
        # accessed from conclude() method in not_equals.py 
        from ._theorems_ import absNotEqZero
        from proveit.number import zero
        if rhs == zero:
            return absNotEqZero.specialize(
                    {a:self.operand}, assumptions=assumptions)
        raise ProofFailure(Equals(self, zero), assumptions,
                "'notEqual' only implemented for a right side of zero")

    # def deduceGreaterThanEqualsZero(self, assumptions=frozenset()):
    #     # not yet clear how to update this method
    #     from ._theorems_ import absIsNonNeg
    #     deduceInComplexes(self.operand, assumptions)
    #     return absIsNonNeg.specialize({a:self.operand}).checked(assumptions)

    def deduceGreaterThanEqualsZero(self, assumptions=USE_DEFAULTS):
        # 03/21/2020 wdc: a first attempt at updating this method
        from proveit.logic import InSet
        from proveit.number import Complexes
        from ._theorems_ import absIsNonNeg
        # InSet(self.operand, Complexes).prove(assumptions=assumptions)
        return absIsNonNeg.specialize({a:self.operand}, assumptions=assumptions)
    
    # def distribute(self, assumptions=frozenset()):
    #     '''
    #     Distribute the absolute value over a product or fraction.
    #     Assumptions may be needed to deduce that the sub-operands are
    #     complex numbers.
    #     '''
    #     from ._theorems_ import absFrac, absProd
    #     from proveit.number import Div, Mult
    #     if isinstance(self.operand, Div):
    #         deduceInComplexes(self.operand.numerator, assumptions)
    #         deduceInComplexes(self.operand.denominator, assumptions)
    #         return absFrac.specialize({a:self.operand.numerator, b:self.operand.denominator}).checked(assumptions)
    #     elif isinstance(self.operand, Mult):
    #         deduceInComplexes(self.operand.operands, assumptions)
    #         return absProd.specialize({xEtc:self.operand.operands}).checked(assumptions)
    #     else:
    #         raise ValueError('Unsupported operand type for absolution value distribution: ', str(self.operand.__class__))

    def distribute(self, assumptions=USE_DEFAULTS):
        '''
        03/21/2020 wdc: a first attempt at updating this method;
        still eliciting an extractInitArgValue error related to a multi-
        variable domain condition for the Mult case. See _demos_ pg
        for an example; WW thinks this is a prob with iterations and
        we'll fix/update this later.
        Distribute the absolute value over a product or fraction.
        Assumptions may be needed to deduce that the sub-operands are
        complex numbers.
        '''
        from ._theorems_ import absFrac, absProd
        from proveit._common_ import n, xx
        from proveit.logic import InSet
        from proveit.number import num, Complexes, Div, Mult
        if isinstance(self.operand, Div):
            return absFrac.specialize(
                    {a:self.operand.numerator, b:self.operand.denominator},
                    assumptions=assumptions)
        elif isinstance(self.operand, Mult):
            from proveit._common_ import xx
            theOperands = self.operand.operands
            return absProd.specialize({n:num(len(theOperands)), xx:theOperands},
                                      assumptions=assumptions)
        else:
            raise ValueError(
                'Unsupported operand type for absolute value distribute() '
                'method: ', str(self.operand.__class__))
    
    def absElimination(self, assumptions=USE_DEFAULTS):
        '''
        For some |x| expression, deduce |x| = x after trying to deduce
        x >= 0. Assumptions may be needed to deduce x >= 0.
        '''
        from ._theorems_ import absElim
        # deduceNonNeg(self.operand, assumptions) # NOT YET IMPLEMENTED
        return absElim.specialize({x:self.operand}, assumptions=assumptions)

    def deduceInNumberSet(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set (such as Integers, Reals, etc),
        attempt to prove that the given expression is in that number
        set using the appropriate closure theorem.
        Created: 3/21/2020 by wdc, based on the same method in the Add
                 and Exp classes.
        Last modified: 3/26/2020 by wdc.
                       Added defaults.checkedAssumptions to avoid
                       ProofFailure error.
        Previously modified: 3/21/2020 by wdc. Creation
        Once established, these authorship notations can be deleted.
        '''
        from proveit.logic import InSet
        from proveit.number.absolute_value._theorems_ import (
                  absComplexClosure, absNonzeroClosure,
                  absComplexClosureNonNegReals)
        from proveit.number import Complexes, Reals, RealsNonNeg, RealsPos

        # among other things, make sure non-existent assumptions
        # manifest as empty tuple () rather than None
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Reals:
            return absComplexClosure.specialize({a:self.operand},
                      assumptions=assumptions)

        if number_set == RealsPos:
            return absNonzeroClosure.specialize({a:self.operand},
                      assumptions=assumptions)

        if number_set == RealsNonNeg:
            return absComplexClosureNonNegReals.specialize({a:self.operand},
                      assumptions=assumptions)

        msg = ("'Abs.deduceInNumberSet()' not implemented for "
               "the %s set"%str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)
