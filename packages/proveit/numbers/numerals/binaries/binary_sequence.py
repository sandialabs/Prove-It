from proveit import (Literal, ExprRange, equality_prover)
from proveit.logic import is_irreducible_value
from proveit.numbers.numerals.numeral import NumeralSequence
from .bit import BITS

class BinarySequence(NumeralSequence):
    # operator of the BinarySequence operation.
    _operator_ = Literal(string_format='Binary', theory=__file__)

    def __init__(self, *bits, styles=None):
        NumeralSequence.__init__(self, BinarySequence._operator_, *bits,
                                 styles=styles)
        self.bits = bits
        for bit in self.bits:
            if is_irreducible_value(bit) and bit not in BITS:
                raise Exception(
                    'A BinarySequence may only be composed of bits')

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        """
        If the BinarySequence contains an ExprRange representing a
        repeated digit, expand it appropriately.
        """
        if self.bits.is_single():
            return self.single_digit_reduction()
        for digit in self.digits:
            if isinstance(digit, ExprRange):
                # if at least one digit is an ExprRange, we can try to 
                # reduce it to an ExprTuple
                return self.digit_repetition_reduction()

    def as_int(self):
        if all(bit in BITS for bit in self.bits):
            return int(self.formatted('string'))
        raise ValueError("Cannot convert %s to an integer; the bits "
                         "are not all irreducible values")
    
    def _prefix(self, format_type):
        if format_type == 'string':
            return 'b' # prefix to indicate a binary representation
        elif format_type == 'latex':
            return r'\texttt{b}'
        else:
            raise ValueError("'format_type', %s, not recognized"%format_type)

    """
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

    """
    
    @equality_prover('single_bit_reduced', 'single_bit_reduce')
    def single_bit_reduction(self, **defaults_config):
        from . import single_bit_reduction
        if not self.bits.is_single():
            raise ValueError("single_digit_reduction is only applicable "
                             "when there is a single digit in the "
                             "BinarySequence; not satisfied by %s"%self)
        return single_bit_reduction.instantiate({n:self.digits[0]})
