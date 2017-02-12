from proveit.logic import Equals, Or, TRUE, FALSE, Forall, inBool
from proveit.common import A, B, Amulti, Bmulti, Cmulti, Aetc, Betc, Cetc
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

orTT = Equals(Or(TRUE, TRUE), TRUE)
orTF = Equals(Or(TRUE, FALSE), TRUE)
orFT = Equals(Or(FALSE, TRUE), TRUE)
orFF = Equals(Or(FALSE, FALSE), FALSE)

# Disjunction only well-defined when each input is a Boolean.
leftInBool = Forall((A, B), inBool(A), conditions=[inBool(Or(A, B))]) 
rightInBool = Forall((A, B), inBool(B), conditions=[inBool(Or(A, B))]) 

# Definition of multi-operand disjunction
emptyDisjunction = Equals(Or(), FALSE) # base case
disjunctionComposition = Forall((A, Bmulti), Equals(Or(A, Betc), Or(A, Or(Betc))))

endAxioms(locals(), __package__)
