from proveit.basiclogic import Implies, Equals, derive_stmt_eq_true
from proveit.common import x, y, P, Px, Py

# hypothesis = (x=y)
hypothesis = Equals(x, y)
# P(x) = P(y) assuming (x=y)
Px_eq_Py = hypothesis.substitution(Px, x).proven({hypothesis})
# P(x) assuming (x=y), P(y)
derive_stmt_eq_true(Py).apply_transitivity(
    Px_eq_Py).derive_via_boolean_equality().proven({hypothesis, Py})
# forall_{P, x, y} {(x = y) => [P(x) => P(y)]}, by (nested) hypothetical
# reasoning
Implies(Equals(x, y), Implies(Py, Px)).generalize((P, x, y)).qed(__file__)
