from proveit.basiclogic import Implies, And, Equals
from proveit.common import a, b, f, x, y, fxy, fab

# hypothesis = (x=a and y=b)
hypothesis = And(Equals(x, a), Equals(y, b))
# f(x, y) = f(a, y) assuming hypothesis
fxy_eq_fay = hypothesis.derive_left().substitution(fxy, x).proven({hypothesis})
# f(a, y) = f(a, b) assuming hypothesis
fay_eq_fab = hypothesis.derive_right().substitution(
    fab, b).proven(
        {hypothesis})
# f(x, y) = f(a, b) assuming hypothesis
conclusion = fxy_eq_fay.apply_transitivity(fay_eq_fab).proven({hypothesis})
# forall_{f, x, y, a, b} (x=a and y=b) => [f(x, y) = f(a, b)]
Implies(hypothesis, conclusion).generalize((f, x, y, a, b)).qed(__file__)
