from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals
from proveit.numbers import Neg, Integer, Real, Complex, Add, Sub, Mult, LessThan, GreaterThan
from proveit.common import a, b, x, y, x_etc, x_multi
from proveit.numbers.common import zero
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

neg_int_closure = Forall(a, InSet(Neg(a), Integer), domain=Integer)
neg_int_closure

neg_real_closure = Forall(a, InSet(Neg(a), Real), domain=Real)
neg_real_closure

neg_complex_closure = Forall(a, InSet(Neg(a), Complex), domain=Complex)
neg_complex_closure

negated_positive_is_negative = Forall(
    a,
    LessThan(
        Neg(a),
        zero),
    domain=Real,
    conditions=[
        GreaterThan(
            a,
            zero)])
negated_positive_is_negative

negated_negative_is_positive = Forall(
    a,
    GreaterThan(
        Neg(a),
        zero),
    domain=Real,
    conditions=[
        LessThan(
            a,
            zero)])
negated_negative_is_positive

neg_not_eq_zero = Forall(
    a,
    NotEquals(
        Neg(a),
        zero),
    domain=Complex,
    conditions=[
        NotEquals(
            a,
            zero)])
neg_not_eq_zero

distribute_neg_through_sum = Forall([x_etc], Equals(
    Neg(Add(x_etc)), Add(Etcetera(Neg(x_multi)))), domain=Complex)
distribute_neg_through_sum


distribute_neg_through_sum_rev = Forall([x_etc],
                                        Equals(Add(Etcetera(Neg(x_multi))),
                                               Neg(Add(x_etc))),
                                        domain=Complex)
distribute_neg_through_sum_rev

distribute_neg_through_subtract = Forall([x, y], Equals(Neg(Sub(x, y)),
                                                        Add(Neg(x), y)),
                                         domain=Complex)
distribute_neg_through_subtract

neg_times_pos = Forall([x, y], Equals(
    Mult(Neg(x), y), Neg(Mult(x, y))), domain=Complex)
neg_times_pos

neg_times_pos_rev = Forall([x, y], Equals(
    Neg(Mult(x, y)), Mult(Neg(x), y)), domain=Complex)
neg_times_pos_rev

pos_times_neg = Forall([x, y], Equals(
    Mult(x, Neg(y)), Neg(Mult(x, y))), domain=Complex)
pos_times_neg

pos_times_neg_rev = Forall([x, y], Equals(
    Neg(Mult(x, y)), Mult(x, Neg(y))), domain=Complex)
pos_times_neg_rev

neg_times_neg = Forall([x, y], Equals(
    Mult(Neg(x), Neg(y)), Mult(x, y)), domain=Complex)
neg_times_neg

neg_neg = Forall([a],
                 Equals(Neg(Neg(a)), a),
                 domain=Complex)
neg_neg

neg_zero = Equals(Neg(zero), zero)
neg_zero

cancel_add_neg = Forall([a, b],
                        Equals(Add(Add(a, b), Neg(b)), a),
                        domain=Complex)
cancel_add_neg


end_theorems(locals(), __package__)
