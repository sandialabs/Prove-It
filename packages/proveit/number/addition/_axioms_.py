from proveit.logic import Forall, InSet, Iff, Equals
from proveit.number import Naturals, NaturalsPos
from proveit.number import Add, GreaterThanEquals
from proveit.common import n, x, xEtc, yEtc, zEtc
from proveit.number.common import zero, one, two
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

zeroAddOne = Equals(Add(zero, one), one)
zeroAddOne

oneAddOne = Equals(Add(one, one), two)
oneAddOne

# base case for composition
addEmpty = Equals(Add(), zero)
addEmpty

addComposition = Forall((x, yEtc), Equals(Add(x, yEtc), Add(x, Add(yEtc))))
addComposition

endAxioms(locals(), __package__)
