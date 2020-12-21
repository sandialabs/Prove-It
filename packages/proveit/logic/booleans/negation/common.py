from proveit import Lambda
from proveit.common import X
from .not_op import Not

negation_map = Lambda(X, Not(X))
double_negation_map = Lambda(X, Not(Not(X)))
