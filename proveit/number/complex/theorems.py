from proveit.statement import Theorems
from proveit.basiclogic.set.setOps import In
from proveit.basiclogic.boolean.boolOps import And
from proveit.number.variables import *
from proveit.basiclogic import Forall, Exists, Equals
from proveit.number.arithmeticOps import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals, Fraction
from proveit.number.arithmeticOps import Add, Subtract, Multiply, Abs, Exponentiate, Neg

setTheorems = Theorems(__package__, locals())

triangleInequality = Forall([a,b],
                        LessThanEquals(Abs(Add(a,b)),Add(Abs(a),Abs(b))),
                        domain=Complexes)

absProd = Forall([a,b],
                 Equals(Abs(Multiply(a,b)),Multiply(Abs(a),Abs(b))),
                 domain = Complexes)

absPow = Forall([a,b,c],
                Equals(Exponentiate(Multiply(a,b),c),
                       Multiply(Exponentiate(a,c),Exponentiate(b,c))
                       ),
                domain = Complexes)

powSum = Forall([a,b,c],
                Equals(Exponentiate(a,Add(b,c)),
                       Multiply(Exponentiate(a,b),Exponentiate(a,c))),
                domain = Complexes)

diffSquareComm = Forall([a,b],
                        Equals(
                            Exponentiate(Subtract(a,b),two),
                            Exponentiate(Subtract(b,a),two)),
                        domain = Complexes)

setTheorems.finish(locals())
