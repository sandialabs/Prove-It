from proveit.logic import Forall, Equals, And, Not, InSet, Intersect, Booleans, TRUE, FALSE
from proveit.common import A, B, Cmulti, Cetc, x
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

intersectionFolding = Forall((x, A, B), InSet(x, Intersect(A, B)), conditions=[And(InSet(x, A), InSet(x, B))])
intersectionFolding

intersectionUnfolding = Forall((x, A, B), And(InSet(x, A), InSet(x, B)), conditions=[InSet(x, Intersect(A, B))])
intersectionUnfolding

intersectionEvalTrue = Forall((x, A, B), Equals(InSet(x, Intersect(A, B)), TRUE), conditions=[InSet(x, A), InSet(x, B)])
intersectionEvalTrue

intersectionEvalViaNotInLeft = Forall((x, A, B), Equals(InSet(x, Intersect(A, B)), FALSE), conditions=[Not(InSet(x, A)), InSet(InSet(x, B), Booleans)])
intersectionEvalViaNotInLeft

intersectionEvalViaNotInRight = Forall((x, A, B), Equals(InSet(x, Intersect(A, B)), FALSE), conditions=[Not(InSet(x, B)), InSet(InSet(x, A), Booleans)])
intersectionEvalViaNotInRight

endTheorems(locals(), __package__)


