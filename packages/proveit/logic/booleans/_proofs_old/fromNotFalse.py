from proveit.basiclogic import Implies, BOOLEANS, FALSE, in_bool, compose, NotEquals
from proveit.common import A

# Anot_f = (A != FALSE)
Anot_f = NotEquals(A, FALSE)
# not_aeq_f = Not(A = FALSE)
not_aeq_f = Anot_f.unfold()
# (A=TRUE or A=FALSE) assuming in_bool(A)
AeqT_or_AeqF = in_bool(A).unfold()
AeqT = AeqT_or_AeqF.operands[0]
# Not(A=FALSE) and (A=TRUE or A=FALSE) assuming each
compose(not_aeq_f, AeqT_or_AeqF).proven({Anot_f, AeqT_or_AeqF})
# in_bool(A=TRUE)
AeqT.deduce_in_bool()
# A assuming in_bool(A), Not(A=FALSE)
AeqT_or_AeqF.derive_left_if_not_right().derive_via_boolean_equality().proven({
    in_bool(A), Anot_f})
# forall_{A in BOOLEANS} Not(A=FALSE) => A
Implies(Anot_f, A).generalize(A, domain=BOOLEANS).qed(__file__)
