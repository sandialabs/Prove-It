from proveit.logic import Equals, Implies, TRUE, FALSE, Forall, And, Iff, Not, Booleans
from proveit.common import A, B
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

# Conveys the defining properties of an implication with a FALSE conclusion
# for any Boolean hypothesis.  This is defined in a manner that enables
# proof by contradiction (reductio ad absurdum).
impliesFalseDef = Forall(A, Equals(Implies(Not(A), FALSE), A), domain=Booleans)

iffDef = Forall((A, B), Equals(Iff(A, B), And(Implies(A, B), Implies(B, A))))

endAxioms(locals(), __package__)
