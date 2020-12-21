from proveit import Etcetera
from proveit.logic import Forall, InSet, NotEquals, Equals
from proveit.numbers import Sub, Natural, NaturalPos, Integer, Real, Complex, Add, Neg, GreaterThan, GreaterThanEquals
from proveit.common import a, b, w, x, y, z, x_etc, y_etc, v_etc, w_etc, z_etc, y_multi
from proveit.numbers.common import zero, one
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

subtract_int_closure = Forall(
    [a, b], InSet(Sub(a, b), Integer), domain=Integer)
subtract_int_closure

subtract_closure_nats = Forall([a, b], InSet(
    Sub(a, b), Natural), domain=Integer, conditions=[GreaterThanEquals(a, b)])
subtract_closure_nats

subtract_closure_nats_pos = Forall([a, b], InSet(
    Sub(a, b), NaturalPos), domain=Integer, conditions=[GreaterThan(a, b)])
subtract_closure_nats_pos

subtract_complex_closure = Forall(
    [a, b], InSet(Sub(a, b), Complex), domain=Complex)
subtract_complex_closure

subtract_real_closure = Forall([a, b], InSet(Sub(a, b), Real), domain=Real)
subtract_real_closure

subtract_one_in_nats = Forall(
    a, InSet(Sub(a, one), Natural), domain=NaturalPos)
subtract_one_in_nats

diff_not_eq_zero = Forall((a, b), NotEquals(
    Sub(a, b), zero), domain=Complex, conditions=[NotEquals(a, b)])
diff_not_eq_zero

subtract_as_add_neg = Forall([x, y], Equals(Sub(x, y),
                                            Add(x, Neg(y))),
                             domain=Complex)
subtract_as_add_neg

add_neg_as_subtract = Forall([x, y], Equals(Add(x, Neg(y)),
                                            Sub(x, y)),
                             domain=Complex)
add_neg_as_subtract


absorb_terms_into_subtraction = Forall([w_etc, x, y, z_etc], Equals(
    Add(w_etc, Sub(x, y), z_etc), Sub(Add(w_etc, x, z_etc), y)), domain=Complex)
absorb_terms_into_subtraction


subtract_cancel_elim_sums = Forall([x, y, z],
                                   Equals(Sub(Add(x, y), Add(x, z)),
                                          Sub(y, z)), domain=Complex)
subtract_cancel_elim_sums

subtract_cancel_elim_left_sum = Forall([w, x, y_etc, z_etc], Equals(
    Sub(Add(w, x), Add(y_etc, w, z_etc)), Sub(x, Add(y_etc, z_etc))), domain=Complex)
subtract_cancel_elim_left_sum

subtract_cancel_elim_right_sum = Forall([w_etc, x, y_etc, z], Equals(
    Sub(Add(w_etc, x, y_etc), Add(x, z)), Sub(Add(w_etc, y_etc), z)), domain=Complex)
subtract_cancel_elim_right_sum

subtract_cancel_two_sums = Forall([v_etc, w, x_etc, y_etc, z_etc],
                                  Equals(Sub(Add(v_etc, w, x_etc), Add(y_etc, w, z_etc)),
                                         Sub(Add(v_etc, x_etc), Add(y_etc, z_etc))), domain=Complex)
subtract_cancel_two_sums

subtract_cancel_left_sum = Forall([x_etc, y, z_etc],
                                  Equals(Sub(Add(x_etc, y, z_etc), y),
                                         Add(x_etc, z_etc)), domain=Complex)
subtract_cancel_left_sum

subtract_cancel_right_sum = Forall([x_etc, y, z_etc], Equals(
    Sub(y, Add(x_etc, y, z_etc)), Neg(Add(x_etc, z_etc))), domain=Complex)
subtract_cancel_right_sum

subtract_cancel_right_sum_single_right = Forall(
    [x, y], Equals(Sub(y, Add(y, x)), Neg(x)), domain=Complex)
subtract_cancel_right_sum_single_right

subtract_cancel_right_sum_single_left = Forall(
    [x, y], Equals(Sub(y, Add(x, y)), Neg(x)), domain=Complex)
subtract_cancel_right_sum_single_left

subtract_cancel_left_sum_single_right = Forall(
    [x, y], Equals(Sub(Add(y, x), y), x), domain=Complex)
subtract_cancel_left_sum_single_right

subtract_cancel_left_sum_single_left = Forall(
    [x, y], Equals(Sub(Add(x, y), y), x), domain=Complex)
subtract_cancel_left_sum_single_left

subtract_cancel_complete = Forall(x, Equals(Sub(x, x), zero), domain=Complex)
subtract_cancel_complete

distribute_subtraction = Forall([x, y_etc],
                                Equals(Sub(x, Add(y_etc)),
                                       Add(x, Etcetera(Neg(y_multi)))),
                                domain=Complex)
distribute_subtraction

cancel_addition = Forall([a, b],
                         Equals(Add(a, Sub(b, b)), a),
                         domain=Complex)
cancel_addition

cancel_sub_and_add = Forall([a, b],
                            Equals(Sub(Sub(a, Neg(b)), b), a),
                            domain=Complex)
cancel_sub_and_add

cancel_sub_then_add = Forall([a, b],
                             Equals(Add(Sub(a, b), b), a),
                             domain=Complex)
cancel_sub_then_add

convert_add_neg_to_sub = Forall([a, b],
                                Equals(Add(a, Neg(b)), Sub(a, b)),
                                domain=Complex)
convert_add_neg_to_sub

end_theorems(locals(), __package__)
