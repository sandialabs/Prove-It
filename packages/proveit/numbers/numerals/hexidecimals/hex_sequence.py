from proveit import (Literal, ExprRange, equality_prover)
from proveit.logic import is_irreducible_value
from proveit.numbers.numerals.numeral import NumeralSequence
from proveit.numbers.numerals import zero, one, two, three, four, five, six, seven, eight, nine, a, b, c, d, e, f
HEXDIGITS = [zero, one, two, three, four, five, six, seven, eight, nine, a, b, c, d, e, f]

class HexSequence(NumeralSequence):
    # operator of the BinarySequence operation.
    _operator_ = Literal(string_format='Hex', theory=__file__)

    def __init__(self, *bits, styles=None):
        NumeralSequence.__init__(self, HexSequence._operator_, *bits,
                                 styles=styles)
        for digit in self.digits:
            if is_irreducible_value(digit) and digit not in HEXDIGITS:
                raise Exception(
                    'A HexSequence may only be composed of 0-f hex digits')

    def as_int(self):
        if all(digit in HEXDIGITS for digit in self.digits):
            return eval(self.formatted('string'))
        raise ValueError("Cannot convert %s to an integer; the hexdigits "
                         "are not all irreducible")
    
    def _prefix(self, format_type):
        if format_type == 'string':
            return 'x' # prefix to indicate a binary representation
        elif format_type == 'latex':
            return r'\textrm{x}'
        else:
            raise ValueError("'format_type', %s, not recognized"%format_type)
