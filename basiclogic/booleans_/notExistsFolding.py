from proveit.basiclogic import *

booleans.qed('notExistsFolding', booleans.notExistsDef.specialize().leftImplViaEquivalence().generalize((P, multiQ)))
