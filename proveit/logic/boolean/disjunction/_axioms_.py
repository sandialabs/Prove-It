from proveit.logic import Equals, Or, TRUE, FALSE, Forall, inBool
from proveit.common import A, B, Amulti, Bmulti, Cmulti, Aetc, Betc, Cetc
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

# base case for composition the Or operation identity
emptyDisjunction = Equals(Or(), FALSE)

disjunctionComposition = Forall((A, Bmulti), Equals(Or(A, Betc), Or(A, Or(Betc))))
disjunctionComposition

disjunctionForBooleansOnly = Forall((Amulti, B, Cmulti), inBool(B), conditions=inBool(Or(Aetc, B, Cetc)))

endAxioms(locals(), __package__)
