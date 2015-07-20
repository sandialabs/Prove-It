from proveit.basiclogic.boolean.axioms import boolsDef
from proveit.basiclogic.set.axioms import singletonDef
from proveit.basiclogic import Implies, In, inBool, Singleton, Union, Equals, TRUE, FALSE, Or
from proveit.basiclogic.variables import x, y, A, X

# hypothesis = (A=TRUE or A=FALSE)
hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
# (A=TRUE) or (A in {FALSE}) assuming hypothesis
singletonDef.specialize({x:A, y:FALSE}).lhsSubstitute(X, Or(Equals(A, TRUE), X)).prove({hypothesis})
# (A in {TRUE}) or (A in {FALSE}) assuming hypothesis
singletonDef.specialize({x:A, y:TRUE}).lhsSubstitute(X, Or(X, In(A, Singleton(FALSE)))).prove({hypothesis})
# [A in ({TRUE} union {FALSE})] assuming hypothesis
In(A, Union(Singleton(TRUE), Singleton(FALSE))).concludeAsFolded()
# (A in BOOLEANS) assuming hypothesis
boolsDef.lhsSubstitute(X, In(A, X)).prove({hypothesis})
# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
Implies(hypothesis, inBool(A)).generalize(A).qed(__file__)
