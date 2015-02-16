from basiclogic import *

# hypothesis = (x=a and y=b)
hypothesis = And(Equals(x, a), Equals(y, b))
# f(x, y) = f(a, y) assuming hypothesis
fxy_eq_fay = hypothesis.deriveLeft().substitution(x, fxy).prove({hypothesis})
# f(a, y) = f(a, b) assuming hypothesis
fay_eq_fab = hypothesis.deriveRight().substitution(b, fab).prove({hypothesis})
# f(x, y) = f(a, b) assuming hypothesis
conclusion = fxy_eq_fay.applyTransitivity(fay_eq_fab).prove({hypothesis})
# forall_{f, x, y, a, b} (x=a and y=b) => [f(x, y) = f(a, b)]
equality.qed('binarySubstitution', Implies(hypothesis, conclusion).generalize((f, x, y, a, b)))
