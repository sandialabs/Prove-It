from .numeral import Numeral, NumeralSequence, is_literal_int
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
