from proveit.logic import Forall, InSet, Iff, Equals
from proveit.number import Naturals, NaturalsPos
from proveit.number import Add, GreaterThanEquals
from proveit.common import n, xEtc, yEtc, zEtc
from proveit.number.common import zero, one, two
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

zeroAddOne = Equals(Add(zero, one), one)
zeroAddOne

oneAddOne = Equals(Add(one, one), two)
oneAddOne

addAssoc = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Add(
                                xEtc,yEtc,zEtc),
                        Add(
                                xEtc,Add(yEtc),zEtc)
                        ),
                  )
addAssoc

endAxioms(locals(), __package__)
