from proveit.basiclogic.boolean.axioms import trueAxiom
from proveit.basiclogic import Implies
from proveit.basiclogic.variables import A

Implies(A, trueAxiom).generalize(A).qed(__file__)
