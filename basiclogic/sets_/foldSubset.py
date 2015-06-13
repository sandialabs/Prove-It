from basiclogic import *

sets.qed('foldSubset', sets.subsetDef.specialize().deriveLeftImplication().generalize((A, B)))
