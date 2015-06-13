from proveit.basiclogic import *

booleans.qed('iffImpliesLeft', Implies(Iff(A, B), Iff(A, B).definition().deriveRightViaEquivalence().deriveRight()).generalize((A, B)))
