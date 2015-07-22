from proveit.basiclogic.equality.axioms import notEqualsDef
from proveit.basiclogic.variables import x, y

notEqualsDef.specialize().leftImplViaEquivalence().generalize((x, y)).qed(__file__)
