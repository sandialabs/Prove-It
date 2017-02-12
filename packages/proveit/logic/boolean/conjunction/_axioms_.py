from proveit.logic import Equals, And, TRUE, FALSE, Forall, Implies, inBool
from proveit.common import A, B, Amulti, Bmulti, Cmulti, Aetc, Betc, Cetc 
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

andTT = Equals(And(TRUE, TRUE), TRUE)
andTF = Equals(And(TRUE, FALSE), FALSE)
andFT = Equals(And(FALSE, TRUE), FALSE)
andFF = Equals(And(FALSE, FALSE), FALSE)

# Conjunction only well-defined when each input is a Boolean.
leftInBool = Forall((A, B), inBool(A), conditions=[inBool(And(A, B))]) 
rightInBool = Forall((A, B), inBool(B), conditions=[inBool(And(A, B))]) 

# Definition of multi-operand conjunction
empytConjunction = Equals(And(), TRUE) # base case
conjunctionComposition = Forall((A, Bmulti), Equals(And(A, Betc), And(A, And(Betc))))

endAxioms(locals(), __package__)
