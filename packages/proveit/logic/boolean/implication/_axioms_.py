from proveit.logic import Equals, Implies, TRUE, FALSE, Forall, And, Iff, Not, Booleans
from proveit.common import A, B
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

# It is tempting to think that we can simply derive this using
# (TRUE => FALSE) = FALSE, and (FALSE => FALSE) = TRUE (the latter can
# derived using hypothetical reasononing without an axiom).  However,
# to get this from those, we ultimately need, it seems, some proofs
# by contradiction that are enabled by this in the first place.
contradictionEval = Forall(A, Equals(Implies(A, FALSE), Not(A)), domain=Booleans)
#impliesTF = Equals(Implies(TRUE, FALSE), FALSE)

iffDef = Forall((A, B), Equals(Iff(A, B), And(Implies(A, B), Implies(B, A))))

endAxioms(locals(), __package__)
