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
equalsSymmetry.instantiate({x:y, y:x}).transpose().proven()
# Not(x=y) assuming (x != y)
NotEquals(x, y).unfold({hypothesis})
# (y != x) assuming Not(x = y)
y_neq_x = Not(Equals(y, x)).deriveNotEquals({Not(Equals(y, x))})
# forall_{x, y} (x != y) => (y != x)
y_neq_x.asImplication({hypothesis}).generalize((x, y)).qed(__file__)
