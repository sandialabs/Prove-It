from proveit.basiclogic.boolean.axioms import iffDef, andFT, impliesTF
from proveit.basiclogic.boolean.theorems import impliesFT
from proveit.basiclogic import TRUE, FALSE, Implies, And, EquationChain
from proveit.basiclogic.variables import A, B, X

eqChain = EquationChain()

# (TRUE <=> FALSE) = [(TRUE => FALSE) and (FALSE => TRUE)]
eqChain.append(iffDef.specialize({A:TRUE, B:FALSE}).prove())
# [(TRUE => FALSE) and (FALSE => TRUE)] = [FALSE and (FALSE => TRUE)]
eqChain.append(impliesTF.substitution(X, And(X, Implies(FALSE, TRUE))).prove())
# [TRUE and (FALSE => TRUE)] = (FALSE and TRUE)
eqChain.append(impliesFT.substitution(X, And(FALSE, X)).prove())
# (FALSE and TRUE) = FALSE
eqChain.append(andFT)
# (TRUE <=> FALSE) = FALSE
eqChain.equateEnds({}).qed(__file__)
