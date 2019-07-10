from proveit.basiclogic.equality.axioms import notEqualsDef
from proveit.basiclogic import Not, Equals, inBool
from proveit.common import x, y, X

# Not(x = y) in BOOLEANS
Not(Equals(x, y)).deduceInBool().proven()
# forall_{x, y} (x != y) in BOOLEANS
notEqualsDef.specialize().subLeftSideInto(inBool(X), X).generalize((x, y)).qed(__file__)
