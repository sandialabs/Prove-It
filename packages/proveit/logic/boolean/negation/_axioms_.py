from proveit.logic import Equals, Not, Implies, Forall, TRUE, FALSE, Booleans, inBool
from proveit.common import A
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

# Implicit in the following set of axioms is that Not(A) is in Booleans iff
# A is in Booleans.  Otherwise, Not(A) is simply undefined.

negationIntro = Forall(A, Not(A), conditions=[Equals(A, FALSE)])

negationElim = Forall(A, Equals(A, FALSE), conditions=[Not(A)])

falsifiedNegationIntro = Forall(A, Equals(Not(A), FALSE), conditions=[A])

falsifiedNegationElim = Forall(A, A, conditions=[Equals(Not(A), FALSE)])

endAxioms(locals(), __package__)
