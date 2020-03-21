from proveit import Literal, Operation, USE_DEFAULTS
from proveit._common_ import a, b, x

class Abs(Operation):
    # operator of the Abs operation.
    _operator_ = Literal(stringFormat='Abs', context=__file__)

    def __init__(self, A):
        Operation.__init__(self, Abs._operator_, A)

    def _closureTheorem(self, numberSet):
        from . import _theorems_
        from proveit.number import Reals, RealsNonNeg, RealsPos
        if numberSet == Reals:
            # complex in, real out
            return _theorems_.absComplexClosure
        elif numberSet == RealsNonNeg:
            # complex in, non-neg real out
            return _theorems_.absComplexClosureNonNegReals
        elif numberSet == RealsPos:
            # nonzero in, real positive out
            return _theorems_.absNonzeroClosure    

    def _notEqZeroTheorem(self):
        from . import _theorems_
        return _theorems_.absNotEqZero
    
    def string(self, **kwargs):
        return '|'+self.operand.string()+'|'

    def latex(self, **kwargs):
        return r'\left|'+self.operand.latex()+r'\right|'

    def deduceGreaterThanEqualsZero(self, assumptions=frozenset()):
        # not yet clear how to update this method
        from ._theorems_ import absIsNonNeg
        deduceInComplexes(self.operand, assumptions)
        return absIsNonNeg.specialize({a:self.operand}).checked(assumptions)

    def distribute(self, assumptions=frozenset()):
        '''
        Distribute the absolute value over a product or fraction.
        Assumptions may be needed to deduce that the sub-operands are in complexes.
        '''
        from .theorems import absFrac, absProd
        from proveit.number import Div, Mult
        if isinstance(self.operand, Div):
            deduceInComplexes(self.operand.numerator, assumptions)
            deduceInComplexes(self.operand.denominator, assumptions)
            return absFrac.specialize({a:self.operand.numerator, b:self.operand.denominator}).checked(assumptions)
        elif isinstance(self.operand, Mult):
            deduceInComplexes(self.operand.operands, assumptions)
            return absProd.specialize({xEtc:self.operand.operands}).checked(assumptions)
        else:
            raise ValueError('Unsupported operand type for absolution value distribution: ', str(self.operand.__class__))
    
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
        Last modified: 3/21/2020 by wdc. Creation
        Once established, these authorship notations can be deleted.
        '''
        from proveit.logic import InSet
        from proveit.number.absolute_value._theorems_ import (
                  absComplexClosure, absNonzeroClosure,
                  absComplexClosureNonNegReals)
        from proveit.number import Complexes, Reals, RealsNonNeg, RealsPos

        if number_set == Reals:
            return absComplexClosure.specialize({a:self.operand},
                      assumptions=assumptions)

        if number_set == RealsPos:
            return absNonzeroClosure.specialize({a:self.operand},
                      assumptions=assumptions)

        if number_set == RealsNonNeg:
            return absComplexClosureNonNegReals.specialize({a:self.operand},
                      assumptions=assumptions)

        msg = "'deduceInNumberSet' not implemented for the %s set"%str(number_set)
        raise ProofFailure(InSet(self, number_set), assumptions, msg)
