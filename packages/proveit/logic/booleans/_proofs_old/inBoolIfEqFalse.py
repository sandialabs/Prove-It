from proveit.basiclogic.booleans.theorems import false_is_bool
from proveit.basiclogic import FALSE, in_bool, Implies, Equals
from proveit.common import A, X

# hypothesis = (A=FALSE)
hypothesis = Equals(A, FALSE)
# in_bool(FALSE)
false_is_bool.proven()
# in_bool(A) assuming hypothesis
conclusion = hypothesis.sub_left_side_into(in_bool(X), X).proven({hypothesis})
# forall_{A} A=FALSE => in_bool(A)
Implies(hypothesis, conclusion).generalize(A).qed(__file__)
