from proveit.basiclogic.set.axioms import superset_def
from proveit.common import A, B

superset_def.instantiate().derive_right_implication().generalize((A, B)).qed(__file__)
