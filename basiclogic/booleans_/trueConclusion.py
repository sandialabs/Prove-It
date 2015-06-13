from basiclogic import *

booleans.qed('trueConclusion', Implies(A, booleans.trueAxiom).generalize(A))
