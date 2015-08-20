from proveit.basiclogic import Implies, Equals
from proveit.common import x, y, P, Px, Py

# hypothesis = (x=y)
hypothesis = Equals(x, y)
# P(x) assuming x=y and P(y)
hypothesis.deriveReversed().lhsSubstitute(x, Px).proven({hypothesis, Py})
# forall_{P, x, y} {(x=y) => [P(x) => P(y)]}
Implies(hypothesis, Implies(Px, Py)).generalize((P, x, y)).qed(__file__)
