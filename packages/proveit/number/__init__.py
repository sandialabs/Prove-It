# Arithmetic and number theory concepts.

from .sets import Integers, Naturals, NaturalsPos, Len, Reals, RealsNeg, RealsPos, Complexes
from .sets import Interval, RealInterval, IntervalOO, IntervalCC, IntervalCO, IntervalOC
from .sets import e, pi, i, infinity
from .numeral import Numeral, num, WholeDecimal
from .numeral import zero, one, two, three, four, five, six, seven, eight, nine, hexa, hexb, hexc, hexd, hexe, hexf
from .addition import Add
from .subtraction import Subtract
from .negation import Neg
from .multiplication import Mult
from .division import Divide, Frac
from .exponentiation import Exp, Sqrt
from .summation import Sum
from .integration import Integrate
from .modular import Abs, Mod, ModAbs
from .rounding import Floor, Ceil, Round
from .ordering import Less, LessEq, LesserSequence, Greater, GreaterEq, GreaterSequence, Min, Max

import proveit

try:
    # Import some fundamental theorems without quantifiers.
    # Fails before running the corresponding _axioms_/_theorems_ notebooks for the first time, but fine after that.
    from .numeral.decimal._theorems_ import add_0_0, add_1_0, add_2_0, add_3_0, add_4_0, add_5_0, add_6_0, add_7_0, add_8_0, add_9_0
    from .numeral.decimal._theorems_ import add_0_1, add_1_1, add_2_1, add_3_1, add_4_1, add_5_1, add_6_1, add_7_1, add_8_1, add_9_1
    from .numeral.decimal._theorems_ import add_0_2, add_1_2, add_2_2, add_3_2, add_4_2, add_5_2, add_6_2, add_7_2, add_8_2, add_9_2
    from .numeral.decimal._theorems_ import add_0_3, add_1_3, add_2_3, add_3_3, add_4_3, add_5_3, add_6_3, add_7_3, add_8_3, add_9_3
    from .numeral.decimal._theorems_ import add_0_4, add_1_4, add_2_4, add_3_4, add_4_4, add_5_4, add_6_4, add_7_4, add_8_4, add_9_4
    from .numeral.decimal._theorems_ import add_0_5, add_1_5, add_2_5, add_3_5, add_4_5, add_5_5, add_6_5, add_7_5, add_8_5, add_9_5
    from .numeral.decimal._theorems_ import add_0_6, add_1_6, add_2_6, add_3_6, add_4_6, add_5_6, add_6_6, add_7_6, add_8_6, add_9_6
    from .numeral.decimal._theorems_ import add_0_7, add_1_7, add_2_7, add_3_7, add_4_7, add_5_7, add_6_7, add_7_7, add_8_7, add_9_7
    from .numeral.decimal._theorems_ import add_0_8, add_1_8, add_2_8, add_3_8, add_4_8, add_5_8, add_6_8, add_7_8, add_8_8, add_9_8
    from .numeral.decimal._theorems_ import add_0_9, add_1_9, add_2_9, add_3_9, add_4_9, add_5_9, add_6_9, add_7_9, add_8_9, add_9_9
except:
    pass
