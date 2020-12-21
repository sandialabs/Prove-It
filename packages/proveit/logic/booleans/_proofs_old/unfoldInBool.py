from proveit.basiclogic.booleans.axioms import bools_def
from proveit.basiclogic.set.axioms import singleton_def
from proveit.basiclogic import Implies, In, in_bool, Singleton, Equals, TRUE, FALSE, Or
from proveit.common import x, y, A, X

# [A in ({TRUE} union {FALSE})] assuming in_bool(A)
AinTunionF = bools_def.sub_right_side_into(In(A, X), X).proven({in_bool(A)})
# (A in {TRUE}) or (A in {FALSE}) assuming in_bool(A)
AinTunionF.unfold().proven({in_bool(A)})
# A=TRUE or (A in {FALSE}) assuming in_bool(A)
singleton_def.instantiate({x: A, y: TRUE}).sub_right_side_into(
    Or(X, In(A, Singleton(FALSE))), X).proven({in_bool(A)})
# A=TRUE or A=FALSE assuming in_bool(A)
conclusion = singleton_def.instantiate({x: A, y: FALSE}).sub_right_side_into(
    Or(Equals(A, TRUE), X), X).proven({in_bool(A)})
# forall_{A} in_bool(A) => (A=TRUE or A=FALSE)
Implies(in_bool(A), conclusion).generalize(A).qed(__file__)
