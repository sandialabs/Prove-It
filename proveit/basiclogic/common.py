from proveit.expression import Operation
from boolean.boolSet import TRUE, FALSE
from equality.eqOps import Equals
from proveit.common import P, fx, gx

PofTrue = Operation(P, TRUE) # P(TRUE)
PofFalse = Operation(P, FALSE) # P(TRUE)
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)
