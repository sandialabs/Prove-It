from proveit.basiclogic import *

# [A in ({TRUE} union {FALSE})] assuming inBool(A)
AinTunionF = booleans.boolsDef.rhsSubstitute(X, In(A, X)).prove({inBool(A)})
# (A in {TRUE}) or (A in {FALSE}) assuming inBool(A)
AinTunionF.unfold().prove({inBool(A)})
# A=TRUE or (A in {FALSE}) assuming inBool(A)
sets.singletonDef.specialize({x:A, y:TRUE}).rhsSubstitute(X, Or(X, In(A, Singleton(FALSE)))).prove({inBool(A)})
# A=TRUE or A=FALSE assuming inBool(A)
conclusion = sets.singletonDef.specialize({x:A, y:FALSE}).rhsSubstitute(X, Or(Equals(A, TRUE), X)).prove({inBool(A)})
# forall_{A} inBool(A) => (A=TRUE or A=FALSE)
booleans.qed('unfoldInBool', Implies(inBool(A), conclusion).generalize(A))
