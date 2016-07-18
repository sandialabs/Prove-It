from proveit.logic import Forall, Equals
from proveit.number import Mult
from proveit.common import xEtc, yEtc, zEtc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

multAssoc = Forall([xEtc,yEtc,zEtc],
                  Equals(
                        Mult(
                                xEtc,yEtc,zEtc),
                        Mult(
                                xEtc,Mult(yEtc),zEtc)
                        )
                  )
multAssoc

endAxioms(locals(), __package__)

