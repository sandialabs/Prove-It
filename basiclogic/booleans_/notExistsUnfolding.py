from basiclogic import *

booleans.qed('notExistsUnfolding', booleans.notExistsDef.specialize().rightImplViaEquivalence().generalize((P, multiQ)))
