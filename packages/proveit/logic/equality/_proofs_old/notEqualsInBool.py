from proveit.basiclogic.equality.axioms import not_equals_def
from proveit.basiclogic import Not, Equals, in_bool
from proveit.common import x, y, X

# Not(x = y) in BOOLEANS
Not(Equals(x, y)).deduce_in_bool().proven()
# forall_{x, y} (x != y) in BOOLEANS
not_equals_def.instantiate().sub_left_side_into(in_bool(X), X).generalize((x, y)).qed(__file__)
