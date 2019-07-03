from proveit.basiclogic.equality.axioms import notEqualsDef
from proveit.common import x, y

notEqualsDef.specialize().rightImplViaEquivalence().generalize((x, y)).qed(__file__)
