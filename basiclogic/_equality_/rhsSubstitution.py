from basiclogic import *

# hypothesis = (x=y)
hypothesis = Equals(x, y)
# P(x) assuming x=y and P(y)
hypothesis.deriveReversed().lhsSubstitute(x, Px).prove({hypothesis, Py})
# forall_{P, x, y} {(x=y) => [P(x) => P(y)]}
equality.qed('rhsSubstitution', Implies(hypothesis, Implies(Px, Py)).generalize((P, x, y)))
