# Arithmetic and number theory concepts.

from .sets import Integers, Naturals, NaturalsPos, Len, Reals, RealsNeg, RealsPos, Complexes
from .sets import Interval, RealInterval, IntervalOO, IntervalCC, IntervalCO, IntervalOC
from .sets import e, pi, i, infinity
from .numeral import num, Numeral, DecimalSequence, DIGITS, isLiteralInt
from .numeral import zero, one, two, three, four, five, six, seven, eight, nine, hexa, hexb, hexc, hexd, hexe, hexf
from .addition import Add, subtract
from .negation import Neg
from .multiplication import Mult
from .division import Div, frac
from .exponentiation import Exp, Sqrt
from .summation import Sum
from .integration import Integrate
from .modular import Abs, Mod, ModAbs
from .rounding import Floor, Ceil, Round
from .ordering import Less, LessEq, LesserSequence, LessOnlySeq, LessEqOnlySeq, lesserSequence, Greater, GreaterEq, GreaterSequence, GreaterOnlySeq, GreaterEqOnlySeq, greaterSequence, Min, Max

import proveit

try:
    # Import some fundamental theorems without quantifiers.
    # Fails before running the corresponding _axioms_/_theorems_ notebooks for the first time, but fine after that.
    from .numeral.deci._theorems_ import less_0_1, less_1_2, less_2_3, less_3_4, less_4_5, less_5_6, less_6_7, less_7_8, less_8_9
    from .numeral.deci._theorems_ import nats_pos_1, nats_pos_2, nats_pos_3, nats_pos_4, nats_pos_5, nats_pos_6, nats_pos_7, nats_pos_8, nats_pos_9
    from .negation._theorems_ import negatedZero
except:
    pass
