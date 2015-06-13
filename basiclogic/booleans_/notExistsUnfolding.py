from proveit.basiclogic import *

booleans.qed('notExistsUnfolding', booleans.notExistsDef.specialize().rightImplViaEquivalence().generalize((P, multiQ)))
