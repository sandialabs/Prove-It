from proveit import (defaults, Literal, Operation, ProofFailure, 
                     USE_DEFAULTS, prover)
from proveit.logic import IrreducibleValue, Equals
from proveit import a, b


class Numeral(Literal, IrreducibleValue):
    _inNaturalStmts = None  # initializes when needed
    _inNaturalPosStmts = None  # initializes when needed
    _inDigitsStmts = None  # initializes when needed
    _notZeroStmts = None  # initializes when needed
    _positiveStmts = None  # initializes when needed

    def __init__(self, n, string_format=None, latex_format=None, *,
                 styles=None):
        if string_format is None:
            string_format = str(n)
        Literal.__init__(
            self, string_format, extra_core_info=[str(n)],
            theory=__file__, styles=styles)
        if not isinstance(n, int):
            raise ValueError("'n' of a Numeral must be an integer")
        self.n = n

    @prover
    def eval_equality(self, other, **defaults_config):
        if other == self:
            return Equals(self, self).prove().evaluation()
        self_neq_other = self.not_equal(other)
        return self_neq_other.unfold().equate_negated_to_false()

    @prover
    def not_equal(self, other, **defaults_config):
        from proveit.numbers import Less
        from proveit.numbers.ordering import less_is_not_eq
        _a, _b = Less.sorted_items([self, other])
        not_eq_stmt = less_is_not_eq.instantiate({a: _a, b: _b})
        if not_eq_stmt.lhs != self:
            # We need to reverse the statement.
            return not_eq_stmt.derive_reversed()
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
    def make_literal(string_format, latex_format, *,
                     extra_core_info, theory, styles):
        '''
        Make the DigitLiteral that matches the core information.
        '''
        from proveit import Theory
        assert theory == Theory(__file__), (
            "Expecting a different Theory for a DigitLiteral: "
            "%s vs %s" % (theory.name, Theory(__file__).name))
        n = int(extra_core_info[0])
        return Numeral(n, string_format, latex_format, styles=styles)

    @prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        from proveit.numbers import (Natural, NaturalPos, 
                                     Digits, IntegerNonPos,
                                     RationalNonPos, RealNonPos)
        from proveit.logic import InSet, SubsetEq
        if number_set == Natural:
            return self.deduce_in_natural()
        elif number_set == NaturalPos:
            return self.deduce_in_natural_pos()
        elif number_set == IntegerNonPos:
            if self.n > 0:
                raise ProofFailure(
                        InSet(self, number_set), defaults.assumptions,
                        "%s is positive"%self)
            return InSet(self, number_set).conclude_as_last_resort()
        elif number_set == Digits:
            return self.deduce_in_digits()
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
                    InSet(self, IntegerNonPos).prove(automation=False)
            except BaseException:
                # Try to prove that it is in the given number
                # set after proving that the numeral is in the
                # Natural set and the NaturalPos set.
                if self.n > 0:
                    self.deduce_in_natural_pos()
                else:
                    self.deduce_in_natural()
                    self.deduce_in_integer_nonpos()
            if self.n > 0:
                sub_rel = SubsetEq(NaturalPos, number_set)
            else:
                if number_set in (RationalNonPos, RealNonPos):
                    sub_rel = SubsetEq(IntegerNonPos, number_set)
                    # Allow automation for this minor thing even
                    # if automation has been disabled coming into this.
                    sub_rel.prove(automation=True)
                else:
                    sub_rel = SubsetEq(Natural, number_set)
            # Prove membership via inclusion:
            return sub_rel.derive_superset_membership(self)

    @prover
    def deduce_in_natural(self, **defaults_config):
        if Numeral._inNaturalStmts is None:
            from proveit.numbers.number_sets.natural_numbers import zero_in_nats
            from .decimals import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
            Numeral._inNaturalStmts = {0: zero_in_nats, 1: nat1, 2: nat2,
                                       3: nat3, 4: nat4, 5: nat5, 6: nat6,
                                       7: nat7, 8: nat8, 9: nat9}
        return Numeral._inNaturalStmts[self.n]

    @prover
    def deduce_in_integer_nonpos(self, **defaults_config):
        from proveit.logic import InSet
        from proveit.numbers import IntegerNonPos
        if self.n != 0:
            raise ProofFailure(InSet(self, IntegerNonPos), defaults.assumptions,
                                "%s is positive"%self)
        from proveit.numbers.number_sets.integers import zero_is_nonpos
        return zero_is_nonpos

    '''
    def deduce_not_zero(self):
        if Numeral._notZeroStmts is None:
            from .decimals import one_not_zero, two_not_zero, three_not_zero, four_not_zero, five_not_zero
            from .decimals import six_not_zero, seven_not_zero, eight_not_zero, nine_not_zero
            Numeral._notZeroStmts = {1:one_not_zero, 2:two_not_zero, 3:three_not_zero, 4:four_not_zero, 5:five_not_zero, 6:six_not_zero, 7:seven_not_zero, 8:eight_not_zero, 9:nine_not_zero}
        return Numeral._notZeroStmts[self.n]
    '''

    @prover
    def deduce_in_natural_pos(self, **defaults_config):
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

    @prover
    def deduce_in_digits(self, **defaults_config):
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

    @prover
    def deduce_positive(self, **defaults_config):
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

    def __init__(self, operator, *digits, styles=None):
        Operation.__init__(self, operator, digits, styles=styles)
        self.digits = self.operands

    def is_irreducible_value(self):
        '''
        Only really an irreducible value if each digit is a Numeral.
        '''
        return (not self.digits.is_single() and
                all(isinstance(digit, Numeral) for digit in self.digits))

    @prover
    def eval_equality(self, other, **defaults_config):
        if other == self:
            return Equals(self, self).conclude_via_reflexivity()
        self_neq_other = self.not_equal(other)
        return self_neq_other.unfold().equate_negated_to_false()


    @prover
    def not_equal(self, other, **defaults_config):
        # same method works for Numeral and NumeralSequence.
        return Numeral.not_equals(self, other)
    
    def _prefix(self, format_type):
        raise NotImplementedError("'_prefix' must be implemented for each "
                                  "NumeralSequence")

    def _formatted(self, format_type, operator=None, **kwargs):
        from proveit import ExprRange
        outstr = ''
        fence = False
        if operator is None:
            operator = ' ~ '
        prefix = self._prefix(format_type)
        if (self.digits.is_single() or 
                not all(isinstance(digit, Numeral) for 
                        digit in self.digits)):
            # for binary, we use #b(...)
            # for hex, we use #x(...)
            # for decimal, #(...)
            if format_type == 'latex':
                outstr += r'\texttt{\#}'
            else:
                outstr += '#'
            outstr += prefix
            outstr += '('
            fence = True
        else:
            if prefix != '':
                # for binary, we use 0b
                # for hex, we use 0x
                # for decimal, no prefix
                if format_type == 'latex':
                    outstr += r'\texttt{0}'
                else:
                    outstr += '0'
            outstr += prefix
        for i, digit in enumerate(self.digits):
            if i != 0 and fence:
                add = operator
            else:
                add = ''
            if isinstance(digit, Operation):
                outstr += add + digit.formatted(format_type, fence=True)
            elif isinstance(digit, ExprRange):
                outstr += add + digit.formatted(format_type, operator=operator)
            else:
                outstr += add + digit.formatted(format_type)
        if fence:
            outstr += r')'
        return outstr

    def _function_formatted(self, format_type, **kwargs):
        return self._formatted(format_type, **kwargs)

def is_literal_int(expr):
    from proveit.numbers import Neg
    if isinstance(expr, Numeral):
        return True
    elif isinstance(expr, NumeralSequence):
        return expr.is_irreducible_value()
    elif isinstance(expr, Neg) and is_literal_int(expr.operand):
        return True
    return False
