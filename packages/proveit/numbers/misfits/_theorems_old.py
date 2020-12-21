'''
Repository for theorems that were born out of expediency but I'd like to get rid of
or generalize to something more appropriate as a named theorem.
'''

from proveit import *
from proveit.logic import *
from proveit.numbers import *
from proveit.common import *
from proveit.numbers.common import *
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

# Poorly named set of inequality theorems added for specific expediant purposes.
# Some day these should be dealt with more appropriately.

div_ineq_thm1 = Forall([a, b, c],
                       LessThanEquals(frac(a, b), frac(c, b)),
                       domain=Real,
                       conditions=(LessThanEquals(a, c), GreaterThan(b, zero))
                       )
div_ineq_thm1

div_ineq_thm1strong = Forall([a, b, c],
                             LessThan(frac(a, b), frac(c, b)),
                             domain=Real,
                             conditions=(LessThan(a, c), GreaterThan(b, zero))
                             )
div_ineq_thm1strong

div_ineq_thm1cor = Forall([a, b, c],
                          LessThanEquals(Mult(b, a), Mult(b, c)),
                          domain=Real,
                          conditions=(LessThanEquals(a, c), GreaterThan(b, zero))
                          )
div_ineq_thm1cor

div_ineq_thm2 = Forall([a, b, c],
                       LessThanEquals(frac(a, b), frac(a, c)),
                       domain=Real,
                       conditions=(
    GreaterThanEquals(b, c),
    GreaterThanEquals(a, zero),
    GreaterThan(b, zero),
    GreaterThan(c, zero)
)
)
div_ineq_thm2

sum_ineq2 = Forall([a, b, c, d], Implies(And(LessThanEquals(a, c), LessThanEquals(
    b, d)), LessThanEquals(Add(a, b), Add(c, d))), domain=Real)
sum_ineq2


ineq_thm5 = Forall([a, b, c],
                   GreaterThanEquals(Mult(c, a), Mult(c, b)),
                   domain=Real,
                   conditions=(GreaterThan(c, zero), GreaterThanEquals(a, b)))
ineq_thm5

pow_ineq = Forall([a, b, c], GreaterThanEquals(Exp(a, b), Exp(
    a, c)), domain=Real, conditions=(GreaterThanEquals(a, one), GreaterThanEquals(b, c)))
pow_ineq

ineq_thm6 = Forall([a, b],
                   GreaterThanEquals(Add(a, b), a),
                   domain=Real,
                   conditions=GreaterThanEquals(b, zero))
ineq_thm6

ineq_thm6a = Forall([a, b],
                    LessThanEquals(Add(a, b), a),
                    domain=Real,
                    conditions=LessThanEquals(b, zero))
ineq_thm6a

ineq_thm7 = Forall([x, l],
                   LessThanEquals(
    frac(one, Exp(Sub(l, x), two)),
    frac(one, Exp(l, two))
),
    domain=Real,
    conditions=(LessThanEquals(l, zero),
                LessThanEquals(zero, x),
                LessThanEquals(x, one)))
ineq_thm7

ineq_thm7a = Forall([x],
                    Forall([a],
                           Forall([l],
                                  LessThanEquals(
                               Mult(a, frac(one, Exp(Sub(l, x), two))),
                               Mult(a, frac(one, Exp(l, two)))
                           ),
                        domain=Integer,
                        conditions=LessThanEquals(l, zero)),
    domain=Real,
    conditions=GreaterThanEquals(a, zero)),
    domain=Real,
    conditions=(LessThanEquals(zero, x),
                LessThanEquals(x, one)))
ineq_thm7a

ineq_thm8 = Forall([x, l],
                   LessThanEquals(
    frac(one, Exp(Sub(l, x), two)),
    frac(one, Exp(Sub(l, one), two)),
),
    domain=Real,
    conditions=(GreaterThan(l, zero),
                LessThanEquals(zero, x),
                LessThanEquals(x, one)))
ineq_thm8

ineq_thm8a = Forall([x],
                    Forall([a],
                           Forall([l],
                                  LessThanEquals(
                               Mult(a, frac(one, Exp(Sub(l, x), two))),
                               Mult(a, frac(one, Exp(Sub(l, one), two))),
                           ),
                        domain=Integer,
                        conditions=GreaterThan(l, zero)),
    domain=Real,
    conditions=GreaterThanEquals(a, zero)),
    domain=Real,
    conditions=(LessThanEquals(zero, x),
                LessThanEquals(x, one)))
ineq_thm8a

ineq_thm9 = Forall(theta, LessThanEquals(
    Abs(Sub(one, Exp(e, Mult(i, theta)))), two), domain=Real)
ineq_thm9

ineq_thm10 = Forall([w, x, y, z], LessThanEquals(w, frac(x, z)),
                    domain=Real,
                    conditions=(LessThanEquals(w, frac(x, y)),
                                GreaterThanEquals(y, z),
                                GreaterThan(w, zero),
                                GreaterThan(x, zero),
                                GreaterThan(y, zero),
                                GreaterThan(z, zero)))
ineq_thm10

ineq_thm10a = Forall([w, x, y, z], LessThanEquals(w, frac(x, z)),
                     domain=Real,
                     conditions=(LessThanEquals(w, frac(x, y)),
                                 GreaterThanEquals(y, z),
                                 GreaterThanEquals(w, zero),
                                 GreaterThan(x, zero),
                                 GreaterThan(y, zero),
                                 GreaterThan(z, zero)))
ineq_thm10a


sum_factor_temp = Forall([a, b, c], Equals(
    Add(Mult(a, b), Mult(a, c)), Mult(a, Add(b, c))), domain=Real)
sum_factor_temp


simplify_quarter_times_two = Equals(Mult(frac(one, four), two), frac(one, two))
simplify_quarter_times_two


bounded_inv_sqrd_integral = Forall([a, b], LessThanEquals(Int(l, frac(one, Exp(l, two)),
                                                              IntervalCC(a, b)),
                                                          frac(one, a)),
                                   domain=RealPos, conditions=[LessThanEquals(a, b)])
bounded_inv_sqrd_integral


inverse_sqrd_is_even_func = InSet(Lambda(l, frac(one, Exp(l, two))), EvenFuncs)
inverse_sqrd_is_even_func


inverse_sqrd_is_mon_dec_func = InSet(
    Lambda(l, frac(one, Exp(l, two))), MonDecFuncs)
inverse_sqrd_is_mon_dec_func

two_squared = Equals(Exp(two, two), four)
two_squared

two_sub_one = Equals(Sub(two, one), one)
two_sub_one

# special theorem for expediency
sub_two_add_one = Forall(a, Equals(Add(Sub(a, two), one),
                                   Sub(a, one)),
                         domain=Complex)
sub_two_add_one

# special theorem for expediency
outer_cancel = Forall((a, b), Equals(Add(a, Sub(b, a)),
                                     b),
                      domain=Complex)
outer_cancel

add_twice = Forall([a],
                   Equals(Add(a, a), Mult(two, a)),
                   domain=Complex)
add_twice

square_pos_ineq = Forall([a],
                         Forall([b],
                                LessThanEquals(Exp(Abs(a), two), Exp(b, two)),
                                domain=Real,
                                conditions=(LessThanEquals(Abs(a), b),)),
                         domain=Complex)
square_pos_ineq

not_eq_iff_diffNotZero = Forall((a, b), Iff(
    NotEquals(a, b), NotEquals(Sub(a, b), zero)), domain=Complex)
not_eq_iff_diffNotZero

sum_integrate_ineq1 = Forall(
    f, Forall(
        [
            a, b], LessThanEquals(
                Sum(
                    x, Operation(
                        f, x), Interval(
                            a, b)), Add(
                                fa, Int(
                                    x, Operation(
                                        f, x), IntervalCC(
                                            a, b)))), domain=Integer, conditions=LessThanEquals(
                                                a, b)), domain=MonDecFuncs)
sum_integrate_ineq1


sum_ineq1 = Forall(
    [
        a, b], Forall(
            [
                m, n], Implies(
                    Forall(
                        k, LessThanEquals(
                            Operation(
                                a, k), Operation(
                                    b, k)), domain=Interval(
                                        m, n)), LessThanEquals(
                                            Sum(
                                                l, Operation(
                                                    a, l), Interval(
                                                        m, n)), Sum(
                                                            l, Operation(
                                                                b, l), Interval(
                                                                    m, n)))), domain=Integer))
sum_ineq1


even_func_sum = Forall(f,
                       Forall([a, b],
                              Equals(Sum(x, Operation(f, x), Interval(a, b)),
                                     Sum(x, Operation(f, x), Interval(Neg(b), Neg(a)))),
                              domain=Integer),
                       domain=EvenFuncs
                       )
even_func_sum

end_theorems(locals(), __package__)
