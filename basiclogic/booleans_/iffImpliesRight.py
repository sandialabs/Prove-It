from basiclogic import *

booleans.qed('iffImpliesRight', Implies(Iff(A, B), Iff(A, B).definition().deriveRightViaEquivalence().deriveLeft()).generalize((A, B)))
