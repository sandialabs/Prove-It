from proveit.basiclogic.equality.theorems import binarySubstitution
from proveit.basiclogic import Implies, And, Equals
from proveit.basiclogic.variables import a, b, c, f, x, y
from proveit.basiclogic.simpleExpr import fab

# hypothesis = (x=a and y=b)
hypothesis = And(Equals(x, a), Equals(y, b))
# [f(x, y) = f(a, b)] assuming hypothesis
fxy_eq_fab = binarySubstitution.specialize().deriveConclusion().prove({hypothesis})
# [f(a, b)=c] => [f(x, y)=c] assuming hypothesis
conclusion = fxy_eq_fab.transitivityImpl(Equals(fab, c)).prove({hypothesis})
# forall_{f, x, y, a, b, c} [x=a and y=b] => {[f(a, b)=c] => [f(x, y)=c]}
Implies(hypothesis, conclusion).generalize((f, x, y, a, b, c)).qed(__file__)
