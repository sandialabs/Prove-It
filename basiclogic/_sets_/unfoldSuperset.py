from basiclogic import *

sets.qed('unfoldSuperset', sets.supersetDef.specialize().deriveRightImplication().generalize((A, B)))
