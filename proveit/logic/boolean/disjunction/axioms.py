from proveit.logic import Equals, Or, TRUE, FALSE, Forall
from proveit.common import A, B, Cetc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

orTT = Equals(Or(TRUE, TRUE), TRUE)
orTT

orTF = Equals(Or(TRUE, FALSE), TRUE)
orTF

orFT = Equals(Or(FALSE, TRUE), TRUE)
orFT

orFF = Equals(Or(FALSE, FALSE), FALSE)
orFF

orComposition = Forall((A, B, Cetc), Equals(Or(A, B, Cetc), Or(A, Or(B, Cetc))))
orComposition

endAxioms(locals(), __package__)
