from proveit.basiclogic.equality.axioms import notEqualsDef
from proveit.basiclogic import Not, Equals, inBool
from proveit.basiclogic.variables import x, y, X

# Not(x = y) in BOOLEANS
Not(Equals(x, y)).deduceInBool().prove()
# forall_{x, y} (x != y) in BOOLEANS
notEqualsDef.specialize().lhsSubstitute(X, inBool(X)).generalize((x, y)).qed(__file__)
