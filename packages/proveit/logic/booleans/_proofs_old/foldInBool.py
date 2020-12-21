from proveit.basiclogic.booleans.axioms import bools_def
from proveit.basiclogic.set.axioms import singleton_def
from proveit.basiclogic import Implies, In, in_bool, Singleton, Union, Equals, TRUE, FALSE, Or
from proveit.common import x, y, A, X

# hypothesis = (A=TRUE or A=FALSE)
hypothesis = Or(Equals(A, TRUE), Equals(A, FALSE))
# (A=TRUE) or (A in {FALSE}) assuming hypothesis
singleton_def.instantiate({x: A, y: FALSE}).sub_left_side_into(
    Or(Equals(A, TRUE), X), X).proven({hypothesis})
# (A in {TRUE}) or (A in {FALSE}) assuming hypothesis
singleton_def.instantiate({x: A, y: TRUE}).sub_left_side_into(
    Or(X, In(A, Singleton(FALSE))), X).proven({hypothesis})
# [A in ({TRUE} union {FALSE})] assuming hypothesis
In(A, Union(Singleton(TRUE), Singleton(FALSE))).conclude_as_folded()
# (A in BOOLEANS) assuming hypothesis
bools_def.sub_left_side_into(In(A, X), X).proven({hypothesis})
# forall_{A} (A=TRUE or A=FALSE) => in_bool(A)
Implies(hypothesis, in_bool(A)).generalize(A).qed(__file__)
