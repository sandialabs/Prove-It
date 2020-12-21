from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit._common_ import a, b, x


class Abs(Operation):
    # operator of the Abs operation.
    _operator_ = Literal(string_format='Abs', theory=__file__)

    def __init__(self, A):
        Operation.__init__(self, Abs._operator_, A)

    def string(self, **kwargs):
        return '|' + self.operand.string() + '|'

    def latex(self, **kwargs):
        return r'\left|' + self.operand.latex() + r'\right|'

    def not_equal(self, rhs, assumptions=USE_DEFAULTS):
        # accessed from conclude() method in not_equals.py
        from ._theorems_ import abs_not_eq_zero
        from proveit.numbers import zero
        if rhs == zero:
            return abs_not_eq_zero.instantiate(
                {a: self.operand}, assumptions=assumptions)
        raise ProofFailure(
            Equals(
                self,
                zero),
            assumptions,
            "'not_equal' only implemented for a right side of zero")

    # def deduce_greater_than_equals_zero(self, assumptions=frozenset()):
    #     # not yet clear how to update this method
    #     from ._theorems_ import abs_is_non_neg
    #     deduce_in_complex(self.operand, assumptions)
    # return abs_is_non_neg.instantiate({a:self.operand}).checked(assumptions)

    def deduce_greater_than_equals_zero(self, assumptions=USE_DEFAULTS):
        # 03/21/2020 wdc: a first attempt at updating this method
        from proveit.logic import InSet
        from proveit.numbers import Complex
        from ._theorems_ import abs_is_non_neg
        # InSet(self.operand, Complex).prove(assumptions=assumptions)
        return abs_is_non_neg.instantiate(
            {a: self.operand}, assumptions=assumptions)

    # def distribute(self, assumptions=frozenset()):
    #     '''
    #     Distribute the absolute value over a product or fraction.
    #     Assumptions may be needed to deduce that the sub-operands are
    #     complex numbers.
    #     '''
    #     from ._theorems_ import abs_frac, abs_prod
    #     from proveit.numbers import Div, Mult
    #     if isinstance(self.operand, Div):
    #         deduce_in_complex(self.operand.numerator, assumptions)
    #         deduce_in_complex(self.operand.denominator, assumptions)
    #         return abs_frac.instantiate({a:self.operand.numerator, b:self.operand.denominator}).checked(assumptions)
    #     elif isinstance(self.operand, Mult):
    #         deduce_in_complex(self.operand.operands, assumptions)
    #         return abs_prod.instantiate({x_etc:self.operand.operands}).checked(assumptions)
    #     else:
    #         raise ValueError('Unsupported operand type for absolution value distribution: ', str(self.operand.__class__))

    def distribute(self, assumptions=USE_DEFAULTS):
        '''
        03/21/2020 wdc: a first attempt at updating this method;
        still eliciting an extract_init_arg_value error related to a multi-
        variable domain condition for the Mult case. See _demos_ pg
        for an example; WW thinks this is a prob with iterations and
        we'll fix/update this later.
        Distribute the absolute value over a product or fraction.
        Assumptions may be needed to deduce that the sub-operands are
        complex numbers.
        '''
        from ._theorems_ import abs_frac, abs_prod
        from proveit._common_ import n, xx
        from proveit.logic import InSet
        from proveit.numbers import num, Complex, Div, Mult
        if isinstance(self.operand, Div):
            return abs_frac.instantiate(
                {a: self.operand.numerator, b: self.operand.denominator},
                assumptions=assumptions)
        elif isinstance(self.operand, Mult):
            from proveit._common_ import xx
            the_operands = self.operand.operands
            return abs_prod.instantiate({n: num(len(the_operands)), xx: the_operands},
                                        assumptions=assumptions)
        else:
            raise ValueError(
                'Unsupported operand type for absolute value distribute() '
                'method: ', str(self.operand.__class__))

    def abs_elimination(self, assumptions=USE_DEFAULTS):
        '''
        For some |x| expression, deduce |x| = x after trying to deduce
        x >= 0. Assumptions may be needed to deduce x >= 0.
        '''
        from ._theorems_ import abs_elim
        # deduce_non_neg(self.operand, assumptions) # NOT YET IMPLEMENTED
        return abs_elim.instantiate({x: self.operand}, assumptions=assumptions)

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given expression is in that number
        set using the appropriate closure theorem.
        Created: 3/21/2020 by wdc, based on the same method in the Add
                 and Exp classes.
        Last modified: 3/26/2020 by wdc.
                       Added defaults.checked_assumptions to avoid
                       ProofFailure error.
        Previously modified: 3/21/2020 by wdc. Creation
        Once established, these authorship notations can be deleted.
        '''
        from proveit.logic import InSet
        from proveit.numbers.absolute_value._theorems_ import (
            abs_complex_closure, abs_nonzero_closure,
            abs_complex_closure_non_neg_real)
        from proveit.numbers import Complex, Real, RealNonNeg, RealPos

        # among other things, make sure non-existent assumptions
        # manifest as empty tuple () rather than None
        assumptions = defaults.checked_assumptions(assumptions)

        if number_set == Real:
            return abs_complex_closure.instantiate({a: self.operand},
                                                   assumptions=assumptions)

        if number_set == RealPos:
            return abs_nonzero_closure.instantiate({a: self.operand},
                                                   assumptions=assumptions)

        if number_set == RealNonNeg:
            return abs_complex_closure_non_neg_real.instantiate(
                {a: self.operand}, assumptions=assumptions)

        msg = ("'Abs.deduce_in_number_set()' not implemented for "
               "the %s set" % str(number_set))
        raise ProofFailure(InSet(self, number_set), assumptions, msg)
