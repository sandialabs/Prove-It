from proveit.basiclogic import *
from forallBoolEvalFalseGeneric import forallBoolEvalFalseDerivation

booleans.qed('forallBoolEvalFalseViaTF', forallBoolEvalFalseDerivation(TRUE, FALSE))
