from proveit.basiclogic.booleans.axioms import true_axiom
from proveit.basiclogic import Implies
from proveit.common import A

Implies(A, true_axiom).generalize(A).qed(__file__)
