# Arithmetic and number theory concepts.

from .sets import (Integer, Natural, NaturalPos,
                   Rationals, RationalsPos, RationalsNonNeg,
                   Reals, RealsNeg, RealsPos, RealsNonNeg, Complexes)
from .sets import Interval, RealInterval, IntervalOO, IntervalCC, IntervalCO, IntervalOC
from .sets import e, pi, i, infinity
from .sets import Rationals, RationalsPos, RationalsNeg, RationalsNonNeg
from .numeral import num, Numeral, DecimalSequence, Digits, DIGITS, isLiteralInt
from .numeral import zero, one, two, three, four, five, six, seven, eight, nine, hexa, hexb, hexc, hexd, hexe, hexf
from .addition import (Add, subtract, dist_subtract, dist_add,
                       const_shift_decomposition, const_shift_composition)
from .negation import Neg
from .multiplication import Mult
from .product import Prod
from .division import Div, frac
from .exponentiation import Exp, sqrt
from .summation import Sum
from .integration import Integrate
from .absolute_value import Abs
from .modular import Mod, ModAbs
from .rounding import Floor, Ceil, Round
from .ordering import Less, LessEq, LesserSequence, LessOnlySeq, LessEqOnlySeq, lesserSequence, Greater, GreaterEq, GreaterSequence, GreaterOnlySeq, GreaterEqOnlySeq, greaterSequence, Min, Max
from .divisibility import Divides, DividesProper, GCD

import proveit

# if proveit.defaults.automation:
#     # Import some fundamental theorems without quantifiers that are
#     # imported when automation is used.
#     from .sets.integer._theorems_ import zeroInNats
#     from .numeral.deci._theorems_ import less_0_1, less_1_2, less_2_3, less_3_4, less_4_5, less_5_6, less_6_7, less_7_8, less_8_9
#     from .numeral.deci._theorems_ import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
#     from .numeral.deci._theorems_ import posnat1, posnat2, posnat3, posnat4, posnat5, posnat6, posnat7, posnat8, posnat9
#     from .negation._theorems_ import negatedZero

if proveit.defaults.automation:
	try:
	    # Import some fundamental theorems without quantifiers that are
      # imported when automation is used.
	    # Fails before running the _axioms_ and _theorems_ notebooks for the first time, but fine after that.
	    from .sets.natural._axioms_ import zero_in_nats
	    from .numeral.deci._theorems_ import less_0_1, less_1_2, less_2_3, less_3_4, less_4_5, less_5_6, less_6_7, less_7_8, less_8_9
	    from .numeral.deci._theorems_ import nat1, nat2, nat3, nat4, nat5, nat6, nat7, nat8, nat9
	    from .numeral.deci._theorems_ import posnat1, posnat2, posnat3, posnat4, posnat5, posnat6, posnat7, posnat8, posnat9
	    from .negation._theorems_ import negatedZero
	except:
	    pass
