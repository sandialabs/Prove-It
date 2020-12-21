from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Iff, And, SetOfAll
from proveit.numbers import Integer, Interval, Real, RealPos, Complex
from proveit.numbers import Abs, Mod, ModAbs, GreaterThanEquals, LessThanEquals, Add, Sub, Neg, Mult, frac, IntervalCO
from proveit.common import a, b, c, x, y, N, x_etc, x_multi
from proveit.numbers.common import zero, one
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

# transferred by wdc 3/11/2020
mod_int_closure = Forall((a, b), InSet(Mod(a, b), Integer), domain=Integer)
mod_int_closure

# transferred by wdc 3/11/2020
mod_in_interval = Forall((a, b), InSet(
    Mod(a, b), Interval(zero, Sub(b, one))), domain=Integer)
mod_in_interval

# transferred by wdc 3/11/2020
mod_real_closure = Forall((a, b), InSet(Mod(a, b), Real), domain=Real)
mod_real_closure

# transferred by wdc 3/11/2020
mod_abs_real_closure = Forall((a, b), InSet(ModAbs(a, b), Real), domain=Real)
mod_abs_real_closure

# transferred by wdc 3/11/2020
abs_complex_closure = Forall([a], InSet(Abs(a), Real), domain=Complex)
abs_complex_closure

# transferred by wdc 3/11/2020
abs_nonzero_closure = Forall(
    [a],
    InSet(
        Abs(a),
        RealPos),
    domain=Complex,
    conditions=[
        NotEquals(
            a,
            zero)])
abs_nonzero_closure

# transferred by wdc 3/11/2020
mod_in_interval_c_o = Forall((a, b), InSet(
    Mod(a, b), IntervalCO(zero, b)), domain=Real)
mod_in_interval_c_o

# transferred by wdc 3/11/2020
abs_is_non_neg = Forall(a, GreaterThanEquals(Abs(a), zero), domain=Complex)
abs_is_non_neg

# transferred by wdc 3/11/2020
abs_not_eq_zero = Forall(
    [a],
    NotEquals(
        Abs(a),
        zero),
    domain=Complex,
    conditions=[
        NotEquals(
            a,
            zero)])
abs_not_eq_zero

# transferred by wdc 3/11/2020
abs_elim = Forall(x, Equals(Abs(x), x),
                  domain=RealPos)
abs_elim

# transferred by wdc 3/11/2020
abs_ineq = Forall(
    (x, y), Iff(
        LessThanEquals(
            Abs(x), y), And(
                LessThanEquals(
                    Neg(y), x), LessThanEquals(
                        x, y))), domain=Real, conditions=[
                            GreaterThanEquals(
                                y, zero)])
abs_ineq

# transferred by wdc 3/11/2020
triangle_inequality = Forall([a, b], LessThanEquals(
    Abs(Add(a, b)), Add(Abs(a), Abs(b))), domain=Complex)
triangle_inequality

# transferred by wdc 3/11/2020
abs_prod = Forall(x_etc,
                  Equals(Abs(Mult(x_etc)),
                         Mult(Etcetera(Abs(x_multi)))),
                  domain=Complex)
abs_prod

# transferred by wdc 3/11/2020
abs_frac = Forall([a, b],
                  Equals(Abs(frac(a, b)), frac(Abs(a), Abs(b))),
                  domain=Complex)
abs_frac

# transferred by wdc 3/11/2020
mod_abs_scaled = Forall(
    (a, b, c), Equals(
        Mult(
            a, ModAbs(
                b, c)), ModAbs(
                    Mult(
                        a, b), Mult(
                            a, c))), domain=Real)
mod_abs_scaled

# transferred by wdc 3/11/2020
mod_abs_subtract_cancel = Forall((a, b, c), LessThanEquals(
    ModAbs(Sub(Mod(Add(b, a), c), b), c), Abs(a)), domain=Real)
mod_abs_subtract_cancel

# transferred by wdc 3/11/2020
full_modular_range_equiv = Forall(
    (N, a, b), Equals(
        SetOfAll(
            x, Mod(
                x, N), domain=Interval(
                    a, b)), Interval(
                        zero, Sub(
                            N, one))), domain=Integer, conditions=[
                                Equals(
                                    Sub(
                                        b, a), Sub(
                                            N, one))])
full_modular_range_equiv

# transferred by wdc 3/11/2020
full_modular_range_equiv_left_shift = Forall(
    (N, a, b, c), Equals(
        SetOfAll(
            x, Mod(
                Add(
                    c, x), N), domain=Interval(
                        a, b)), Interval(
                            zero, Sub(
                                N, one))), domain=Integer, conditions=[
                                    Equals(
                                        Sub(
                                            b, a), Sub(
                                                N, one))])
full_modular_range_equiv_left_shift

# transferred by wdc 3/11/2020
full_modular_range_equiv_right_shift = Forall(
    (N, a, b, c), Equals(
        SetOfAll(
            x, Mod(
                Add(
                    x, c), N), domain=Interval(
                        a, b)), Interval(
                            zero, Sub(
                                N, one))), domain=Integer, conditions=[
                                    Equals(
                                        Sub(
                                            b, a), Sub(
                                                N, one))])
full_modular_range_equiv_right_shift


end_theorems(locals(), __package__)
