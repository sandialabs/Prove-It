from proveit.statement import Theorems
from proveit.basiclogic.set.setOps import In
from proveit.basiclogic.boolean.boolOps import And
from proveit.number.variables import *
from proveit.basiclogic import Forall, Exists, Equals
from proveit.number.arithmeticOps import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals, Fraction
from proveit.number.arithmeticOps import Add, Subtract, Multiply, Abs, Exponentiate, Neg

setTheorems = Theorems(__package__, locals())

inReals = Forall(a,In(a,Reals),domain=Integers)

setTheorems.finish(locals())
