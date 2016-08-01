# Common expressions involving basiclogic operations acting on common Variables.

from proveit import Operation
from proveit.logic.boolean.booleans import TRUE, FALSE
from equality.equals import Equals
from proveit.common import P, fx, gx

PofTrue = Operation(P, TRUE) # P(TRUE)
PofFalse = Operation(P, FALSE) # P(TRUE)
fx_eq_gx = Equals(fx, gx) # f(x) = g(x)
