from proveit.basiclogic.equality.axioms import notEqualsDef
from proveit.basiclogic.variables import x, y

notEqualsDef.specialize().rightImplViaEquivalence().generalize((x, y)).qed(__file__)
