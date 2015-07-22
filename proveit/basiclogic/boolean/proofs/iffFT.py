from proveit.basiclogic.boolean.axioms import iffDef, andTF, impliesTF
from proveit.basiclogic.boolean.theorems import impliesFT
from proveit.basiclogic import TRUE, FALSE, Implies, And, EquationChain
from proveit.common import A, B, X

eqChain = EquationChain()

# (FALSE <=> TRUE) = [(FALSE => TRUE) and (TRUE => FALSE)]
eqChain.append(iffDef.specialize({A:FALSE, B:TRUE}).prove())
# [(FALSE => TRUE) and (TRUE => FALSE)] = [TRUE and (TRUE => FALSE)]
eqChain.append(impliesFT.substitution(X, And(X, Implies(TRUE, FALSE))).prove())
# [TRUE and (TRUE => FALSE)] = (TRUE and FALSE)
eqChain.append(impliesTF.substitution(X, And(TRUE, X)).prove())
# (TRUE and FALSE) = FALSE
eqChain.append(andTF)
# (FALSE <=> TRUE) = FALSE
eqChain.equateEnds({}).qed(__file__)
