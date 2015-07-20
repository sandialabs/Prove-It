from proveit.basiclogic.boolean.axioms import boolsDef
from proveit.basiclogic.set.axioms import singletonDef
from proveit.basiclogic import Implies, In, inBool, Singleton, Equals, TRUE, FALSE, Or
from proveit.basiclogic.variables import x, y, A, X

# [A in ({TRUE} union {FALSE})] assuming inBool(A)
AinTunionF = boolsDef.rhsSubstitute(X, In(A, X)).prove({inBool(A)})
# (A in {TRUE}) or (A in {FALSE}) assuming inBool(A)
AinTunionF.unfold().prove({inBool(A)})
# A=TRUE or (A in {FALSE}) assuming inBool(A)
singletonDef.specialize({x:A, y:TRUE}).rhsSubstitute(X, Or(X, In(A, Singleton(FALSE)))).prove({inBool(A)})
# A=TRUE or A=FALSE assuming inBool(A)
conclusion = singletonDef.specialize({x:A, y:FALSE}).rhsSubstitute(X, Or(Equals(A, TRUE), X)).prove({inBool(A)})
# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
Implies(inBool(A), conclusion).generalize(A).qed(__file__)
