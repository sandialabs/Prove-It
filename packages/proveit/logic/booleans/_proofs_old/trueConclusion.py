from proveit.basiclogic.booleans.axioms import trueAxiom
from proveit.basiclogic import Implies
from proveit.common import A

Implies(A, trueAxiom).generalize(A).qed(__file__)
