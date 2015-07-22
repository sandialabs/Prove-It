from proveit.basiclogic import Implies, Not, Equals, NotEquals
from proveit.basiclogic.equality.axioms import equalsSymmetry
from proveit.common import x, y

# hypothesis = (x != y)
hypothesis = NotEquals(x, y)
# inBool(x=y)
Equals(x, y).deduceInBool()
# inBool(y=x)
Equals(y, x).deduceInBool()
# Not(x=y) => Not(y=x)
equalsSymmetry.specialize({x:y, y:x}).transpose().prove()
# Not(x=y) assuming (x != y)
NotEquals(x, y).unfold().prove({hypothesis})
# (y != x) assuming Not(x = y)
Not(Equals(y, x)).deriveNotEquals().prove({Not(Equals(y, x))})
# forall_{x, y} (x != y) => (y != x)
Implies(hypothesis, NotEquals(y, x)).generalize((x, y)).qed(__file__)
