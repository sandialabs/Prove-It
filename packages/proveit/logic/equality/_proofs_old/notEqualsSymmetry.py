from proveit.basiclogic import Implies, Not, Equals, NotEquals
from proveit.basiclogic.equality.axioms import equals_symmetry
from proveit.common import x, y

# hypothesis = (x != y)
hypothesis = NotEquals(x, y)
# in_bool(x=y)
Equals(x, y).deduce_in_bool()
# in_bool(y=x)
Equals(y, x).deduce_in_bool()
# Not(x=y) => Not(y=x)
equals_symmetry.instantiate({x:y, y:x}).transpose().proven()
# Not(x=y) assuming (x != y)
NotEquals(x, y).unfold({hypothesis})
# (y != x) assuming Not(x = y)
y_neq_x = Not(Equals(y, x)).derive_not_equals({Not(Equals(y, x))})
# forall_{x, y} (x != y) => (y != x)
y_neq_x.as_implication({hypothesis}).generalize((x, y)).qed(__file__)
