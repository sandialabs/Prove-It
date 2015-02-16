from basiclogic import *

equality.qed('unfoldNotEquals', equality.notEqualsDef.specialize().rightImplViaEquivalence().generalize((x, y)))
