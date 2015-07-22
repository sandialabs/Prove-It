from proveit.basiclogic import Implies
from proveit.common import A

Implies(A, A).generalize(A).qed(__file__)
