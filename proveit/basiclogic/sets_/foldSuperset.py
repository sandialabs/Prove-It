from proveit.basiclogic import *

sets.qed('foldSuperset', sets.supersetDef.specialize().deriveLeftImplication().generalize((A, B)))
