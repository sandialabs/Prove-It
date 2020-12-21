
# coding: utf-8

# In[1]:

from proveit.logic import Forall, Exists, NotExists, Boolean, TRUE, FALSE, in_bool, Not, And, Or, Implies, Iff, Equals, NotEquals
from proveit.common import A, B, C, P, Q, R, S, x, y, PofA, Qetc, Retc, x_etc, y_etc, z_etc, Px_etc, Py_etc, Pxy_etc, etc_Qx_etc, etc_Qy_etc, etc_Ry_etc
from proveit.logic.common import PofTrue, PofFalse
from proveit import begin_theorems, end_theorems


begin_theorems(locals())

true_eq_true = Equals(TRUE, TRUE)

true_eq_true_eval = Equals(Equals(TRUE, TRUE), TRUE)

false_eq_false = Equals(FALSE, FALSE)

false_eq_false_eval = Equals(Equals(FALSE, FALSE), TRUE)

true_not_false = NotEquals(TRUE, FALSE)

not_equals_false = Forall(A, NotEquals(A, FALSE), conditions=[A])

true_eq_false_eval = Equals(Equals(TRUE, FALSE), FALSE)

false_eq_true_eval = Equals(Equals(FALSE, TRUE), FALSE)

true_conclusion = Forall(A, Implies(A, TRUE))

in_bool_equiv = Forall(A, Equals(in_bool(A), Or(Equals(A, TRUE), Equals(A, FALSE))))

true_is_bool = in_bool(TRUE)

false_is_bool = in_bool(FALSE)

unfold_forall_over_bool = Forall(P, Implies(Forall(A, PofA, domain=Boolean), And(PofTrue, PofFalse)))

in_bool_if_true = Forall(A, in_bool(A), conditions=[A])

in_bool_if_false = Forall(A, in_bool(A), conditions=[Not(A)])

# This weak form requires B to be a Boolean
by_cases_weak = Forall((A, B), B, domain=Boolean, conditions=[Implies(A, B), Implies(Not(A), B)])

# This is a stronger form that does not require B to be a Boolean
by_cases = Forall(A, Forall(B, B, conditions=[Implies(A, B), Implies(Not(A), B)]), domain=Boolean)

fold_forall_over_bool = Forall(P, Forall(A, PofA, domain = Boolean), conditions=[PofTrue, PofFalse])

forall_bool_eval_true = Forall(P, Equals(Forall(A, PofA, domain=Boolean), TRUE),  conditions=[PofTrue, PofFalse])

# uses constructive dilemma
unfold_is_bool = Forall(A, Or(A, Not(A)), domain=Boolean)







from_not_false = Forall(A, A, domain=Boolean, conditions=[NotEquals(A, FALSE)])


not_in_bool_equiv = Forall(A, Equals(in_bool(A), And(NotEquals(A, TRUE), NotEquals(A, FALSE))))



end_theorems(locals(), __package__)




