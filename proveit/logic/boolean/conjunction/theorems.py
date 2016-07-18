from proveit.logic import And, TRUE, Forall, inBool, BOOLEANS
from proveit.common import A, B
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

trueAndTrue = And(TRUE, TRUE)
trueAndTrue

conjunctionIntro = Forall((A, B), And(A, B), conditions=(A, B))
conjunctionIntro

conjunctionClosure = Forall((A, B), inBool(And(A, B)), domain=BOOLEANS)
conjunctionClosure

endTheorems(locals(), __package__)
