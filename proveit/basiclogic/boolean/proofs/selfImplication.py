from proveit.basiclogic import Implies
from proveit.basiclogic.variables import A

Implies(A, A).generalize(A).qed(__file__)
