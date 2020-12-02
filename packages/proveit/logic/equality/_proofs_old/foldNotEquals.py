from proveit.basiclogic.equality.axioms import notEqualsDef
from proveit.common import x, y

notEqualsDef.instantiate().leftImplViaEquivalence().generalize((x, y)).qed(__file__)
