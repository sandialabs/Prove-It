from proveit.basiclogic import *

# hypothesis = (A=TRUE or A=FALSE)
hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
# (A=TRUE) or (A in {FALSE}) assuming hypothesis
sets.singletonDef.specialize({x:A, y:FALSE}).lhsSubstitute(X, Or(Equals(A, TRUE), X)).prove({hypothesis})
# (A in {TRUE}) or (A in {FALSE}) assuming hypothesis
sets.singletonDef.specialize({x:A, y:TRUE}).lhsSubstitute(X, Or(X, In(A, Singleton(FALSE)))).prove({hypothesis})
# [A in ({TRUE} union {FALSE})] assuming hypothesis
In(A, Union(Singleton(TRUE), Singleton(FALSE))).concludeAsFolded()
# (A in BOOLEANS) assuming hypothesis
booleans.boolsDef.lhsSubstitute(X, In(A, X)).prove({hypothesis})
# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
booleans.qed('foldInBool', Implies(hypothesis, inBool(A)).generalize(A))
