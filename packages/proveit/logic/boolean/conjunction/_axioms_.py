from proveit.logic import Equals, And, TRUE, FALSE, Forall, Implies, inBool
from proveit.common import A, B, Amulti, Bmulti, Cmulti, Aetc, Betc, Cetc 
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

andTT = Equals(And(TRUE, TRUE), TRUE)
andTT

andTF = Equals(And(TRUE, FALSE), FALSE)
andTF

andFT = Equals(And(FALSE, TRUE), FALSE)
andFT

andFF = Equals(And(FALSE, FALSE), FALSE)
andFF

# base case for composition with the And operation identity
empytConjunction = Equals(And(), TRUE)

conjunctionComposition = Forall((A, Bmulti), Equals(And(A, Betc), And(A, And(Betc))))
conjunctionComposition

conjunctionForBooleansOnly = Forall((Amulti, B, Cmulti), inBool(B), conditions=inBool(And(Aetc, B, Cetc)))

endAxioms(locals(), __package__)
