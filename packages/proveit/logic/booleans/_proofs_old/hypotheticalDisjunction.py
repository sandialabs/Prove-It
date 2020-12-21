from proveit.basiclogic.booleans.axioms import not_t
from proveit.basiclogic import BOOLEANS, FALSE, in_bool, Implies, And, Or, Not, derive_stmt_eq_true
from proveit.common import A, B, C, X

AorB = Or(A, B)
hypothesis = And(Implies(A, C), Implies(B, C))
ABCareBool = {in_bool(A), in_bool(B), in_bool(C)}
# A=>C, B=>C assuming (A=>C and B=>C)
AimplC, _ = hypothesis.decompose()
# Not(A) assuming in_bool(A), in_bool(B), (A=>C and B=>C), Not(C)
AimplC.transpose().derive_conclusion().proven({in_bool(A), in_bool(C), hypothesis, Not(C)})
# B assuming in_bool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
AorB.derive_right_if_not_left().proven(ABCareBool | {hypothesis, AorB, Not(C)})
# Not(TRUE) assuming in_bool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
derive_stmt_eq_true(C).sub_right_side_into(Not(X), X).proven(ABCareBool | {hypothesis, AorB, Not(C)})
# FALSE assuming in_bool(A, B, C), (A=>C and B=>C), (A or B), Not(C)
not_t.derive_right_via_equality().proven(ABCareBool | {hypothesis, AorB, Not(C)})
# Contradiction proof of C assuming (A=>C and B=>C), (A or B), in_bool(A), and in_bool(B)
Implies(Not(C), FALSE).derive_via_contradiction().proven(ABCareBool | {hypothesis, AorB})
# forall_{A, B, C in BOOLEANS} (A=>C and B=>C) => ((A or B) => C)
Implies(hypothesis, Implies(AorB, C)).generalize((A, B, C), domain=BOOLEANS).qed(__file__)
