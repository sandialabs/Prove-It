from proveit.basiclogic.booleans.axioms import implicit_not_f, implicit_not_t
from proveit.basiclogic import Implies, Not, derive_stmt_eq_true
from proveit.common import A

# hypothesis: Not(Not(A))
hypothesis = Not(Not(A))
# [Not(Not(A)) = TRUE] assuming hypothesis
derive_stmt_eq_true(hypothesis).proven({hypothesis})
# [Not(A) = FALSE] assuming hypothesis
implicit_not_f.instantiate({A:Not(A)}).derive_conclusion().proven({hypothesis})
# A assuming hypothesis
implicit_not_t.instantiate().derive_conclusion().derive_via_boolean_equality().proven({hypothesis})
# forall_{A} Not(Not(A)) => A
Implies(Not(Not(A)), A).generalize(A).qed(__file__)
