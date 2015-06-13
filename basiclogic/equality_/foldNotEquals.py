from basiclogic import *

equality.qed('foldNotEquals', equality.notEqualsDef.specialize().leftImplViaEquivalence().generalize((x, y)))
