from proveit.basiclogic import *

sets.qed('unfoldSetOfAll', sets.setOfAllDef.specialize().deriveRightImplication().generalize((P, f, x)))
