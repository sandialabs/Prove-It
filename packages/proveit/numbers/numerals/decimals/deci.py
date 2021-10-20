from proveit import (Literal, USE_DEFAULTS, Operation, ExprRange, defaults,
                     prover, relation_prover, equality_prover)
from proveit import a, b, c, d, k, m, n, x
from proveit.logic import is_irreducible_value
from proveit.numbers.number_sets.number_set import NumberSet, NumberMembership
from proveit.numbers.numerals.numeral import NumeralSequence, Numeral
from proveit.numbers.numerals import zero, one, two, three, four, five, six, seven, eight, nine
DIGITS = [zero, one, two, three, four, five, six, seven, eight, nine]


class DecimalSequence(NumeralSequence):
    # operator of the DecimalSequence operation.
    _operator_ = Literal(string_format='Decimal', theory=__file__)

    def __init__(self, *digits, styles=None):
        NumeralSequence.__init__(self, DecimalSequence._operator_, *digits,
                                 styles=styles)
        for digit in self.digits:
            if is_irreducible_value(digit) and digit not in DIGITS:
                raise Exception(
                    'A DecimalSequence may only be composed of 0-9 digits')

    def _prefix(self, format_type):
        # No prefix for a DecimalSequence (unlike binary or hex
        # which needs a prefix to indicate type of number it is).
        return ""

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        """
        If the DecimalSequence contains an ExprRange representing a
        repeated digit, expand it appropriately.
        """
        from proveit import ExprRange
        if self.digits.is_single():
            return self.single_digit_reduction()
        for digit in self.digits:
            if isinstance(digit, ExprRange):
                # if at least one digit is an ExprRange, we can try to 
                # reduce it to an ExprTuple
                return self.digit_repetition_reduction()

    def as_int(self):
        if all(digit in DIGITS for digit in self.digits):
            return eval(self.formatted('string'))
        raise ValueError("Cannot convert %s to an integer; its digits "
                         "are not all irreducible")

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        from proveit.numbers import Natural, NaturalPos
        from proveit.logic import InSet
        if number_set == Natural:
            return self.deduce_in_natural()
        elif number_set == NaturalPos:
            return self.deduce_in_natural_pos()
        else:
            try:
                # Do this to avoid infinite recursion -- if
                # we already know this numeral is in NaturalPos
                # we should know how to prove that it is in any
                # number set that contains the natural numbers.
                if self.as_int() > 0:
                    InSet(self, NaturalPos).prove(automation=False)
                else:
                    InSet(self, Natural).prove(automation=False)
            except BaseException:
                # Try to prove that it is in the given number
                # set after proving that the numeral is in
                # the Natural set and the NaturalPos set.
                self.deduce_in_natural()
                if self.as_int() > 0:
                    self.deduce_in_natural_pos()
            return InSet(self, number_set).conclude()

    @relation_prover
    def deduce_in_natural(self, **defaults_config):
        from . import deci_sequence_is_nat
        return deci_sequence_is_nat.instantiate(
                {n: self.operands.num_elements(), a: self.digits})
        # if Numeral._inNaturalStmts is None:
        #     from proveit.numbers.number_sets.integers import zero_in_nats
        #     from proveit.numbers.numerals.decimals import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
        #     Numeral._inNaturalStmts = {0: zero_in_nats, 1: nat1, 2: nat2, 3: nat3, 4: nat4, 5: nat5, 6: nat6, 7: nat7,
        #                                 8: nat8, 9: nat9}
        # return Numeral._inNaturalStmts[self.n]

    @relation_prover
    def deduce_in_natural_pos(self, **defaults_config):
        from . import deci_sequence_is_nat_pos
        return deci_sequence_is_nat_pos.instantiate(
            {n: self.operands.num_elements(), a: self.digits})
        # from proveit import ProofFailure
        # if Numeral._inNaturalPosStmts is None:
        #     from proveit.numbers.numerals.decimals import posnat1, posnat2, posnat3, posnat4, posnat5
        #     from proveit.numbers.numerals.decimals import posnat6, posnat7, posnat8, posnat9
        #     Numeral._inNaturalPosStmts = {1: posnat1, 2: posnat2, 3: posnat3, 4: posnat4, 5: posnat5, 6: posnat6,
        #                                    7: posnat7, 8: posnat8, 9: posnat9}
        # if self.n <= 0:
        #     raise ProofFailure(self, [],
        #                        "Cannot prove %d in NaturalPos" % self.n)
        # return Numeral._inNaturalPosStmts[self.n]

    @equality_prover('single_digit_reduced', 'single_digit_reduce')
    def single_digit_reduction(self, **defaults_config):
        from . import single_digit_reduction
        if not self.digits.is_single():
            raise ValueError("single_digit_reduction is only applicable "
                             "when there is a single digit in the "
                             "DecimalSequence; not satisfied by %s"%self)
        return single_digit_reduction.instantiate({n:self.digits[0]})

    @equality_prover('digit_repetition_reduced', 'digit_repetition_reduce')
    def digit_repetition_reduction(self, **defaults_config):
        '''
        Tries to reduce a decimal sequence containing an ExprRange.
        For example, reduce #(3 4 2 .. 4 repeats .. 2 3) to 3422223
        '''
        from proveit import TransRelUpdater
        from proveit.core_expr_types.tuples import n_repeats_reduction
        from proveit.numbers.numerals.decimals import deci_sequence_reduction_ER

        expr = self
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self)

        idx = 0
        for i, digit in enumerate(self.digits):
            # i is the current index in the original expression
            # idx is the current index in the transformed expression (eq.relation)
            if (isinstance(digit, ExprRange) and 
                    isinstance(digit.body, Numeral)):
                import proveit.numbers.numerals.decimals

                # _m = expr.digits[:i].num_elements(assumptions)
                # _n = digit.end_index
                # _k = expr.digits[i + 1:].num_elements(assumptions)
                # _a = expr.digits[:i]
                # _b = digit.body
                # _d = expr.digits[i + 1:]

                _m = eq.relation.rhs.digits[:idx].num_elements()
                _n = digit.end_index
                _k = expr.digits[i + 1:].num_elements()
                _a = eq.relation.rhs.digits[:idx]
                _b = digit.body
                _d = expr.digits[i + 1:]

                # if digit.end_index.as_int() >= 10:
                # Automatically reduce an Expression range of
                # a single numeral to an Expression tuple
                # (3 .. 4 repeats.. 3) = 3333
                # #(2 3 4 (5 ..3 repeats.. 5) 6 7 8) = 234555678

                while _n.as_int() > 9:
                    _x = digit.body

                    _c = n_repeats_reduction.instantiate(
                            {n: _n, x: _x}, preserve_all=True).rhs

                    eq.update(deci_sequence_reduction_ER.instantiate(
                        {m: _m, n: _n, k: _k, a: _a, b: _b, c: _c, d: _d},
                        preserve_all=True))
                    _n = num(_n.as_int() - 1)
                    idx += 1

                #_n = digit.end_index
                len_thm = proveit.numbers.numerals.decimals \
                    .__getattr__('reduce_%s_repeats' % _n)
                _x = digit.body

                _c = len_thm.instantiate({x: _x}).rhs

                idx += _n.as_int()

                eq.update(deci_sequence_reduction_ER.instantiate(
                    {m: _m, n: _n, k: _k, a: _a, b: _b, c: _c, d: _d},
                    preserve_all=True))
            else:
                idx += 1

        return eq.relation

    @prover
    def num_add_eval(self, num2, **defaults_config):
        '''
        evaluates the addition of two integers
        '''
        from . import md_only_nine_add_one, md_nine_add_one
        num1 = self
        if isinstance(num2, int):
            num2 = num(num2)
        if num2 == one:
            # if the second number (num2) is one, we set it equal to the first number and then assume the
            # first number to be one and the second number to not be one.  SHOULD BE DELETED once addition works
            # for numbers greater than one.
            num2 = num1
        elif num2 != one:
            raise NotImplementedError(
                "Currently, num_add_eval only works for the addition of Decimal "
                "Sequences and one, not %s, %s" %
                (str(num1), str(num2)))
        if all(digit == nine for digit in num2.digits):
            # every digit is 9
            return md_only_nine_add_one.instantiate(
                {k: num2.digits.num_elements()})
        elif num2.digits[-1] == nine:
            # the last digit is nine
            count = 0
            idx = -1
            while num2.digits[idx] == nine or (
                isinstance(
                    num2.digits[idx],
                    ExprRange) and num2.digits[idx].body == nine):
                if isinstance(num2.digits[idx], ExprRange):
                    count += num2.digits[idx].end_index
                else:
                    count += 1
                idx -= 1
            length = num2.digits.num_elements()
            _m = num(length.as_int() - count - 1)
            _k = num(count)
            _a = num2.digits[:-(count + 1)]
            _b = num2.digits[-(count + 1)]
            return md_nine_add_one.instantiate(
                {m: _m, k: _k, a: _a, b: _b})
        else:
            # the last digit is not nine
            _m = num(num2.digits.num_elements().as_int() - 1)
            _k = num(0)
            _a = num2.digits[:-1]
            _b = num2.digits[-1]
        eq = md_nine_add_one.instantiate(
            {m: _m, k: _k, a: _a, b: _b})
        return eq.inner_expr(
        ).rhs.operands[-1].evaluate()

    '''
    # Shouldn't be needed given new auto-simplification approach.
    def evaluate_add_digit(self, assumptions=USE_DEFAULTS):
        """
        Evaluates each addition within the DecimalSequence
        """
        from proveit import TransRelUpdater, ExprTuple
        from proveit.numbers import Add
        from . import deci_sequence_reduction

        expr = self
        # A convenience to allow successive update to the equation via transitivities.
        # (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        for i, digit in enumerate(self.digits):
            if isinstance(digit, Add):
                # only implemented for addition.

                _m = expr.digits[:i].num_elements(assumptions=assumptions)
                _n = digit.operands.num_elements(assumptions=assumptions)
                _k = expr.digits[i + 1:].num_elements(assumptions=assumptions)
                # _a = expr.inner_expr().operands[:i]
                _b = digit.operands
                _c = digit.evaluation(assumptions=assumptions).rhs
                # _d = expr.inner_expr().operands[i + 1:]

                _a = expr.digits[:i]
                _d = expr.digits[i + 1:]

                expr = eq.update(deci_sequence_reduction.instantiate(
                    {m: _m, n: _n, k: _k, a: _a, b: _b, c: _c, d: _d}, assumptions=assumptions))

        return eq.relation
    '''


class DigitSet(NumberSet):
    def __init__(self, *, styles=None):
        NumberSet.__init__(
            self, 'Digits', r'\mathbb{N}^{\leq 9}',
            theory=__file__, styles=styles)

    @prover
    def deduce_member_lower_bound(self, member, **defaults_config):
        from . import digits_lower_bound
        return digits_lower_bound.instantiate({n: member})

    @prover
    def deduce_member_upper_bound(self, member, **defaults_config):
        from . import digits_upper_bound
        return digits_upper_bound.instantiate({n: member})

    def membership_object(self, element):
        return DeciMembership(element, self)


class DeciMembership(NumberMembership):
    '''
        Defines methods that apply to membership of a decimal sequence.
    '''

    def __init__(self, element, number_set):
        NumberMembership.__init__(self, element, number_set)

    @prover
    def conclude(self, **defaults_config):
        from proveit import ProofFailure
        from . import n_in_digits
        # if we know the element is 0-9, then we can show it is a digit
        try:
            return NumberMembership.conclude(self)
        except ProofFailure:
            return n_in_digits.instantiate({n: self.element})

        # if isinstance(self.element, numeral) and 0 <= self.element.as_int() <= 9:
        #     _n = self.element.as_int()
        #     thm = proveit.numbers.numerals.decimals \
        #         .__getattr__('digit%s' % _n)
        #     return thm
        # else:
        # return n_in_digits.instantiate({n: self.element},
        # assumptions=assumptions)

    def side_effects(self, judgment):
        '''
        Yield side-effects when proving 'n in Digit' for a given n.
        '''
        yield self.derive_element_lower_bound
        yield self.derive_element_upper_bound

    @prover
    def derive_element_lower_bound(self, **defaults_config):
        return self.domain.deduce_member_lower_bound(self.element)

    @prover
    def derive_element_upper_bound(self, **defaults_config):
        return self.domain.deduce_member_upper_bound(self.element)


def num(x):
    from proveit.numbers import Neg
    if x < 0:
        return Neg(num(abs(x)))
    if isinstance(x, int):
        if x < 10:
            if x == 0:
                return zero
            elif x == 1:
                return one
            elif x == 2:
                return two
            elif x == 3:
                return three
            elif x == 4:
                return four
            elif x == 5:
                return five
            elif x == 6:
                return six
            elif x == 7:
                return seven
            elif x == 8:
                return eight
            elif x == 9:
                return nine
        else:
            return DecimalSequence(*[num(int(digit)) for digit in str(x)])
    else:
        assert False, 'num not implemented for anything except integers currently. plans to take in strings or floats with specified precision'
