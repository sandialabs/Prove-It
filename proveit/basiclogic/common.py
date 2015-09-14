# Common expressions involving basiclogic operations acting on common Variables.

from proveit.expression import Operation
from boolean.boolSet import TRUE, FALSE
from equality.eqOps import Equals
from proveit.common import n, P, fx, gx, xEtc, yEtc, zEtc
from proveit.number.natural.counting import ExprListCount

PofTrue = Operation(P, TRUE) # P(TRUE)
PofFalse = Operation(P, FALSE) # P(TRUE)
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)
n_of_xEtc = Equals(ExprListCount(xEtc), n)
n_of_yEtc = Equals(ExprListCount(yEtc), n)
n_of_zEtc = Equals(ExprListCount(zEtc), n)