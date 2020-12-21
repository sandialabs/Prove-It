from proveit.basiclogic.booleans.theorems import true_is_bool
from proveit.basiclogic import TRUE, in_bool, Implies, Equals
from proveit.common import A, X

# hypothesis = (TRUE=A)
hypothesis = Equals(TRUE, A)
# in_bool(TRUE)
true_is_bool.proven()
# in_bool(A) assuming hypothesis
conclusion = hypothesis.sub_right_side_into(in_bool(X), X).proven({hypothesis})
# forall_{A} (TRUE=A) => in_bool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
