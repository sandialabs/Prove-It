from proveit.basiclogic import *
from forallBoolEvalFalseGeneric import forallBoolEvalFalseDerivation

booleans.qed('forallBoolEvalFalseViaFT', forallBoolEvalFalseDerivation(FALSE, TRUE))
