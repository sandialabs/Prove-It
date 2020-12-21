from proveit.basiclogic import BOOLEANS, TRUE, FALSE, in_bool, Implies, And, derive_stmt_eq_true, Equals
from proveit.common import A, P, PofA
from proveit.basiclogic.common import PofTrue, PofFalse

# hypothesis = [P(TRUE) and P(FALSE)]
hypothesis = And(PofTrue, PofFalse)
# in_bool(A=TRUE), in_bool(A=FALSE), in_bool(P(A) = TRUE)
AeqT = Equals(A, TRUE)
AeqF = Equals(A, FALSE)
PofAeqT = Equals(PofA, TRUE)
for eq_expr in (AeqT, AeqF, PofAeqT):
    eq_expr.deduce_in_bool()
# P(TRUE), P(FALSE) assuming hypothesis
for case in hypothesis.decompose(): case.proven({hypothesis})
# A=TRUE => P(A)=TRUE assuming hypothesis
Implies(AeqT, derive_stmt_eq_true(AeqT.sub_left_side_into(PofA, A))).proven({hypothesis})
# A=FALSE => P(A)=TRUE assuming hypothesis
Implies(AeqF, derive_stmt_eq_true(AeqF.sub_left_side_into(PofA, A))).proven({hypothesis})
# P(A) assuming hypothesis, (A in BOOLEANS)
in_bool(A).unfold().derive_common_conclusion(PofAeqT).derive_via_boolean_equality().proven({hypothesis, in_bool(A)})
# forall_{P} P(TRUE) and P(FALSE) => forall_{A in BOOLEANS} P(A)
Implies(hypothesis, PofA.generalize(A, domain=BOOLEANS)).generalize(P).qed(__file__)
