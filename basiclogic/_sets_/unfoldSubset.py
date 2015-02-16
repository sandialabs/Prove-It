from basiclogic import *

sets.qed('unfoldSubset', sets.subsetDef.specialize().deriveRightImplication().generalize((A, B)))
