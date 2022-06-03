from .numeral import (Numeral, NumeralSequence, 
                      is_numeric_natural, is_numeric_int, 
                      is_numeric_rational,
                      numeric_rational_ints,
                      simplified_numeric_rational,
                      less_numeric_ints,
                      less_eq_numeric_ints,
                      less_numeric_rationals,
                      less_eq_numeric_rationals)
#from .binaries import BinarySequence, binnum
#from .hexidecimals import HexSequence, hexnum


# KEEP THE FOLLOWING IN __init__.py FOR THEORY PACKAGES.
#  Make additions above, or add to sys.modules[__name__].__dict__ below.
# This allows us to import common expression, axioms, and theorems of
# the theory package directly from the package.
import sys
from proveit._core_.theory import TheoryPackage
sys.modules[__name__] = TheoryPackage(__name__, __file__, locals())

# TODO: change Digits to Digit (consistent with Integer, Real, etc)
from .decimals import Digits, DIGITS, DecimalSequence, num
from .binaries import Bit, BITS, BinarySequence
sys.modules[__name__].__dict__.update(locals())
