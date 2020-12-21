from proveit.basiclogic import Implies, Equals, FALSE
from proveit.common import A

# FeqA := (F=A)
FeqA = Equals(FALSE, A)
# Not(A) assuming FeqA
not_a = FeqA.derive_reversed().derive_via_boolean_equality().proven({FeqA})
Implies(FeqA, not_a).generalize(A).qed(__file__)
