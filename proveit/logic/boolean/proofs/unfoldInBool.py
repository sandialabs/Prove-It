from proveit.basiclogic.boolean.axioms import boolsDef
from proveit.basiclogic.set.axioms import singletonDef
from proveit.basiclogic import Implies, In, inBool, Singleton, Equals, TRUE, FALSE, Or
from proveit.common import x, y, A, X

# [A in ({TRUE} union {FALSE})] assuming inBool(A)
AinTunionF = boolsDef.rhsSubstitute(In(A, X), X).proven({inBool(A)})
# (A in {TRUE}) or (A in {FALSE}) assuming inBool(A)
AinTunionF.unfold().proven({inBool(A)})
# A=TRUE or (A in {FALSE}) assuming inBool(A)
singletonDef.specialize({x:A, y:TRUE}).rhsSubstitute(Or(X, In(A, Singleton(FALSE))), X).proven({inBool(A)})
# A=TRUE or A=FALSE assuming inBool(A)
conclusion = singletonDef.specialize({x:A, y:FALSE}).rhsSubstitute(Or(Equals(A, TRUE), X), X).proven({inBool(A)})
# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
Implies(inBool(A), conclusion).generalize(A).qed(__file__)
