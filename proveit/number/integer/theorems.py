from proveit.statement import Theorems
from proveit.basiclogic.set.setOps import In
from proveit.basiclogic.boolean.boolOps import And
from proveit.number.variables import *
from proveit.basiclogic import Forall, Exists, Equals
from proveit.number.arithmeticOps import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals, Fraction
from proveit.number.arithmeticOps import Add, Subtract, Multiply, Abs, Exponentiate, Neg, Summation, DiscreteContiguousSet
from proveit.number.arithmeticOps import Integrate

setTheorems = Theorems(__package__, locals())

inReals = Forall(a,In(a,Reals),domain=Integers)

indexShift = Forall(f,
       Forall([a,b,c],Equals(Summation(x,Operation(f,x),DiscreteContiguousSet(a,b)),
              Summation(x,Operation(f,Subtract(x,c)),DiscreteContiguousSet(Add(a,c),Add(b,c)))),domain=Integers))

sumIntegrateIneq1 = Forall(f,
                    Forall([a,b],LessThanEquals(Summation(x,Operation(f,x),DiscreteContiguousSet(a,b)),
                    Integrate(x,Operation(f,x),DiscreteContiguousSet(Subtract(a,one),b))),
                    domain=Integers,conditions=LessThanEquals(a,b)),
                    domain=MonDecFuncs)


setTheorems.finish(locals())
