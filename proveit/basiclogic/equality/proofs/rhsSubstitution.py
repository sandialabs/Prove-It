from proveit.basiclogic import Implies, Equals
from proveit.basiclogic.variables import x, y, P
from proveit.basiclogic.simpleExpr import Px, Py

# hypothesis = (x=y)
hypothesis = Equals(x, y)
# P(x) assuming x=y and P(y)
hypothesis.deriveReversed().lhsSubstitute(x, Px).prove({hypothesis, Py})
# forall_{P, x, y} {(x=y) => [P(x) => P(y)]}
Implies(hypothesis, Implies(Px, Py)).generalize((P, x, y)).qed(__file__)
