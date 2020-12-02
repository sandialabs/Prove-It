from proveit.basiclogic.boolean.axioms import boolsDef
from proveit.basiclogic.set.axioms import singletonDef
from proveit.basiclogic import Implies, In, inBool, Singleton, Union, Equals, TRUE, FALSE, Or
from proveit.common import x, y, A, X

# hypothesis = (A=TRUE or A=FALSE)
hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
# (A=TRUE) or (A in {FALSE}) assuming hypothesis
singletonDef.instantiate({x:A, y:FALSE}).subLeftSideInto(Or(Equals(A, TRUE), X), X).proven({hypothesis})
# (A in {TRUE}) or (A in {FALSE}) assuming hypothesis
singletonDef.instantiate({x:A, y:TRUE}).subLeftSideInto(Or(X, In(A, Singleton(FALSE))), X).proven({hypothesis})
# [A in ({TRUE} union {FALSE})] assuming hypothesis
In(A, Union(Singleton(TRUE), Singleton(FALSE))).concludeAsFolded()
# (A in BOOLEANS) assuming hypothesis
boolsDef.subLeftSideInto(In(A, X), X).proven({hypothesis})
# forall_{A} (A=TRUE or A=FALSE) => inBool(A)
Implies(hypothesis, inBool(A)).generalize(A).qed(__file__)
