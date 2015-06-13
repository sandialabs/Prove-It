from basiclogic import *

booleans.qed('notExistsFolding', booleans.notExistsDef.specialize().leftImplViaEquivalence().generalize((P, multiQ)))
