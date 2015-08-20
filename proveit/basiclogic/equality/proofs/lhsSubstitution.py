from proveit.basiclogic import Implies, Equals, deriveStmtEqTrue
from proveit.common import x, y, P, Px, Py

# hypothesis = (x=y)
hypothesis = Equals(x, y)
# P(x) = P(y) assuming (x=y)
Px_eq_Py = hypothesis.substitution(x, Px).proven({hypothesis})
# P(x) assuming (x=y), P(y)
deriveStmtEqTrue(Py).applyTransitivity(Px_eq_Py).deriveViaBooleanEquality().proven({hypothesis, Py})
# forall_{P, x, y} {(x = y) => [P(x) => P(y)]}, by (nested) hypothetical reasoning
Implies(Equals(x, y), Implies(Py, Px)).generalize((P, x, y)).qed(__file__)
