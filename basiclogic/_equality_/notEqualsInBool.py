from basiclogic import *

# Not(x = y) in BOOLEANS
Not(Equals(x, y)).deduceInBool().prove()
# forall_{x, y} (x != y) in BOOLEANS
equality.qed('notEqualsInBool', equality.notEqualsDef.specialize().lhsSubstitute(X, inBool(X)).generalize((x, y)))
