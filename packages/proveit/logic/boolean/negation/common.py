from proveit import Lambda
from proveit.common import X
from not_op import Not

negationMap = Lambda(X, Not(X))
doubleNegationMap = Lambda(X, Not(Not(X)))
