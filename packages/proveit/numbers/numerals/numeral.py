from proveit import defaults, Literal, Operation, ProofFailure, USE_DEFAULTS
from proveit.logic import IrreducibleValue, Equals
from proveit import a, b


class Numeral(Literal, IrreducibleValue):
    _inNaturalStmts = None  # initializes when needed
    _inNaturalPosStmts = None  # initializes when needed
    _inDigitsStmts = None  # initializes when needed
    _notZeroStmts = None  # initializes when needed
    _positiveStmts = None  # initializes when needed

    def __init__(self, n, string_format=None, latex_format=None):
        if string_format is None:
            string_format = str(n)
        Literal.__init__(
            self, string_format, extra_core_info=[
                str(n)], theory=__file__)
        if not isinstance(n, int):
            raise ValueError("'n' of a Numeral must be an integer")
        self.n = n

    def eval_equality(self, other, assumptions=USE_DEFAULTS):
        if other == self:
            return Equals(self, self).prove().evaluation()
        self_neq_other = self.not_equal(other, assumptions)
        return self_neq_other.unfold().equate_negated_to_false()

    def not_equal(self, other, assumptions=USE_DEFAULTS):
        from proveit.numbers import Less
        from proveit.numbers.ordering import less_is_not_eq
        _a, _b = Less.sorted_items([self, other], assumptions=assumptions)
        not_eq_stmt = less_is_not_eq.instantiate(
            {a: _a, b: _b}, assumptions=assumptions)
        if not_eq_stmt.lhs != self:
            # We need to reverse the statement.
            return not_eq_stmt.derive_reversed(assumptions)
        return not_eq_stmt       
    
    def remake_arguments(self):
        '''
        Yield the argument values that could be used to recreate this DigitLiteral.
        '''
        yield self.n
        if self.string_format != str(self.n):
            yield '"' + self.string_format + '"'
        if self.latex_format != self.string_format:
            yield ('latex_format', 'r"' + self.latex_format + '"')

    def as_int(self):
        return self.n

    @staticmethod
    def make_literal(string_format, latex_format, extra_core_info, theory):
        '''
        Make the DigitLiteral that matches the core information.
        '''
        from proveit import Theory
        assert theory == Theory(__file__), (
            "Expecting a different Theory for a DigitLiteral: "
            "%s vs %s" % (theory.name, Theory(__file__).name))
        n = int(extra_core_info[0])
        return Numeral(n, string_format, latex_format)

    def deduce_in_number_set(self, number_set, assumptions=USE_DEFAULTS):
        from proveit.numbers import Natural, NaturalPos, Digits
        from proveit.logic import InSet
        if number_set == Natural:
            return self.deduce_in_natural(assumptions)
        elif number_set == NaturalPos:
            return self.deduce_in_natural_pos(assumptions)
        elif number_set == Digits:
            return self.deduce_in_digits(assumptions)
        else:
            try:
                # Do this to avoid infinite recursion -- if
                # we already know this numeral is in the NaturalPos set
                # we should know how to prove that it is in any
                # number set that contains the natural numbers.
                if self.n > 0:
                    InSet(self, NaturalPos).prove(automation=False)
                else:
                    InSet(self, Natural).prove(automation=False)
            except BaseException:
                # Try to prove that it is in the given number
                # set after proving that the numeral is in the
                # Natural set and the NaturalPos set.
                self.deduce_in_natural()
                if self.n > 0:
                    self.deduce_in_natural_pos()
            return InSet(self, number_set).conclude(assumptions)

    def deduce_in_natural(self, assumptions=USE_DEFAULTS):
        if Numeral._inNaturalStmts is None:
            from proveit.numbers.number_sets.natural_numbers import zero_in_nats
            from .decimals import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
            Numeral._inNaturalStmts = {0: zero_in_nats, 1: nat1, 2: nat2,
                                       3: nat3, 4: nat4, 5: nat5, 6: nat6,
                                       7: nat7, 8: nat8, 9: nat9}
        return Numeral._inNaturalStmts[self.n]

    '''
    def deduce_not_zero(self):
        if Numeral._notZeroStmts is None:
            from .decimals import one_not_zero, two_not_zero, three_not_zero, four_not_zero, five_not_zero
            from .decimals import six_not_zero, seven_not_zero, eight_not_zero, nine_not_zero
            Numeral._notZeroStmts = {1:one_not_zero, 2:two_not_zero, 3:three_not_zero, 4:four_not_zero, 5:five_not_zero, 6:six_not_zero, 7:seven_not_zero, 8:eight_not_zero, 9:nine_not_zero}
        return Numeral._notZeroStmts[self.n]
    '''

    def deduce_in_natural_pos(self, assumptions=USE_DEFAULTS):
        if Numeral._inNaturalPosStmts is None:
            from .decimals import posnat1, posnat2, posnat3, posnat4, posnat5
            from .decimals import posnat6, posnat7, posnat8, posnat9
            Numeral._inNaturalPosStmts = {
                1: posnat1,
                2: posnat2,
                3: posnat3,
                4: posnat4,
                5: posnat5,
                6: posnat6,
                7: posnat7,
                8: posnat8,
                9: posnat9}
        if self.n <= 0:
            raise ProofFailure(self, [],
                               "Cannot prove %d in NaturalPos" % self.n)
        return Numeral._inNaturalPosStmts[self.n]

    def deduce_in_digits(self, assumptions=USE_DEFAULTS):
        if Numeral._inDigitsStmts is None:
            from .decimals import digit0, digit1, digit2, digit3, digit4, digit5
            from .decimals import digit6, digit7, digit8, digit9
            Numeral._inDigitsStmts = {
                0: digit0,
                1: digit1,
                2: digit2,
                3: digit3,
                4: digit4,
                5: digit5,
                6: digit6,
                7: digit7,
                8: digit8,
                9: digit9}
        if self.n < 0 or self.n > 9:
            raise ProofFailure(self, [],
                               "Cannot prove %d in Digits" % self.n)
        return Numeral._inDigitsStmts[self.n]

    def deduce_positive(self, assumptions=USE_DEFAULTS):
        if Numeral._positiveStmts is None:
            from .decimals import posnat1, posnat2, posnat3, posnat4, posnat5
            from .decimals import posnat6, posnat7, posnat8, posnat9
            Numeral._positiveStmts = {
                1: posnat1,
                2: posnat2,
                3: posnat3,
                4: posnat4,
                5: posnat5,
                6: posnat6,
                7: posnat7,
                8: posnat8,
                9: posnat9}
        return Numeral._positiveStmts[self.n]


class NumeralSequence(Operation, IrreducibleValue):
    """
    Base class of BinarySequence, DecimalSequence, and HexSequence.
    """

    def __init__(self, operator, *digits):
        from proveit import ExprRange
        Operation.__init__(self, operator, digits)
        # if len(digits) <= 1 and not isinstance(digits[0], ExprRange):
        #     raise Exception('A NumeralSequence should have two or more digits.  Single digit number should be represented as the corresponding Literal.')
        self.digits = self.operands

    def eval_equality(self, other, assumptions=USE_DEFAULTS):
        if other == self:
            return Equals(self, self).prove()
        pass  # need axioms/theorems to prove inequality amongst different numerals

    def not_equal(self, other, assumptions=USE_DEFAULTS):
        # same method works for Numeral and NumeralSequence.
        return Numeral.not_equals(self, other, assumptions=assumptions)

    def _formatted(self, format_type, **kwargs):
        from proveit import ExprRange, var_range
        outstr = ''

        for digit in self.digits:
            if isinstance(digit, Operation):
                outstr += digit.formatted(format_type, fence=True)
            elif isinstance(digit, ExprRange):
                outstr += digit.formatted(format_type, operator=' ')
            else:
                outstr += digit.formatted(format_type)
        return outstr
        # return ''.join(digit.formatted(format_type) for digit in self.digits)


def is_literal_int(expr):
    from proveit.numbers import Neg
    if isinstance(expr, Numeral):
        return True
    elif isinstance(expr, NumeralSequence):
        return True
    elif isinstance(expr, Neg) and is_literal_int(expr.operand):
        return True
    return False
