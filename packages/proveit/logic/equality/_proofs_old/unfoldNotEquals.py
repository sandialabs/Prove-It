from proveit.basiclogic.equality.axioms import notEqualsDef
from proveit.common import x, y

notEqualsDef.instantiate().rightImplViaEquivalence().generalize((x, y)).qed(__file__)
