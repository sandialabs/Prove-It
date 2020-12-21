from proveit.basiclogic import Implies, Iff
from proveit.common import A, B

Implies(Iff(A, B), Iff(A, B).definition().derive_right_via_equality().derive_left()).generalize((A, B)).qed(__file__)
