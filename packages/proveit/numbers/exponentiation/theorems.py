from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals
from proveit.numbers import Integer, Natural, NaturalPos, Real, RealPos, Complex
from proveit.numbers import Exp, sqrt, Add, Mult, Sub, Neg, frac, Abs, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals
from proveit.common import a, b, c, d, n, x, y, z, x_etc, x_multi
from proveit.numbers.common import zero, one, two
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

exp_nat_closure = Forall((a, b), InSet(
    Exp(a, b), NaturalPos), domain=Natural, conditions=[NotEquals(a, zero)])
exp_nat_closure

exp_real_closure = Forall([a, b], InSet(Exp(a, b), Real), domain=Real, conditions=[
                          GreaterThanEquals(a, zero), GreaterThan(b, zero)])
exp_real_closure

exp_real_pos_closure = Forall([a, b], InSet(Exp(a, b), RealPos), domain=Real,
                              conditions=[GreaterThan(a, zero)])
exp_real_pos_closure

exp_complex_closure = Forall([a, b], InSet(Exp(a, b), Complex), domain=Complex,
                             conditions=[NotEquals(a, zero)])
exp_complex_closure

sqrt_real_closure = Forall([a], InSet(sqrt(a), Real), domain=Real,
                           conditions=[GreaterThanEquals(a, zero)])
sqrt_real_closure

sqrt_real_pos_closure = Forall([a], InSet(sqrt(a), RealPos), domain=RealPos)
sqrt_real_pos_closure

sqrt_complex_closure = Forall([a], InSet(sqrt(a), Complex), domain=Complex)
sqrt_complex_closure

# Should generalize to even power closure, but need to define and
# implement evens set to do this.
sqrd_pos_closure = Forall(a, InSet(Exp(a, two), RealPos),
                          domain=Real, conditions=[NotEquals(a, zero)])
sqrd_pos_closure

square_pos_ineq = Forall([a, b],
                         LessThanEquals(Exp(Abs(a), two), Exp(b, two)),
                         domain=Real,
                         conditions=(LessThanEquals(Abs(a), b),))
square_pos_ineq

square_pos_eq = Forall(a,
                       Equals(Exp(Abs(a), two), Exp(a, two)),
                       domain=Real)
square_pos_eq

exp_not_eq_zero = Forall([a, b], NotEquals(
    Exp(a, b), zero), domain=Complex, conditions=[NotEquals(a, zero)])
exp_not_eq_zero

exp_zero_eq_one = Forall([a], Equals(Exp(a, zero), one),
                         domain=Complex, conditions=[NotEquals(a, zero)])
exp_zero_eq_one

exponentiated_zero = Forall([x], Equals(
    Exp(zero, x), zero), domain=Complex, conditions=[NotEquals(x, zero)])
exponentiated_zero

exponentiated_one = Forall([x], Equals(Exp(one, x), one), domain=Complex)
exponentiated_one

sum_in_exp = Forall([a, b, c],
                    Equals(Exp(a, Add(b, c)),
                           Mult(Exp(a, b), Exp(a, c))),
                    domain=Complex, conditions=[NotEquals(a, zero)])
sum_in_exp

sum_in_exp_rev = Forall([a, b, c],
                        Equals(Mult(Exp(a, b), Exp(a, c)),
                               Exp(a, Add(b, c))),
                        domain=Complex, conditions=[NotEquals(a, zero)])
sum_in_exp_rev

add_one_right_in_exp = Forall([a, b],
                              Equals(Exp(a, Add(b, one)),
                                     Mult(Exp(a, b), a)),
                              domain=Complex, conditions=[NotEquals(a, zero)])
add_one_right_in_exp

add_one_right_in_exp_rev = Forall([a, b], Equals(Mult(Exp(a, b), a), Exp(
    a, Add(b, one))), domain=Complex, conditions=[NotEquals(a, zero)])
add_one_right_in_exp_rev


add_one_left_in_exp = Forall([a, b],
                             Equals(Exp(a, Add(one, b)),
                                    Mult(a, Exp(a, b))),
                             domain=Complex, conditions=[NotEquals(a, zero)])
add_one_left_in_exp

add_one_left_in_exp_rev = Forall([a, b], Equals(Mult(a, Exp(a, b)), Exp(
    a, Add(one, b))), domain=Complex, conditions=[NotEquals(a, zero)])
add_one_left_in_exp_rev


diff_in_exp = Forall([a, b, c],
                     Equals(Exp(a, Sub(b, c)),
                            Mult(Exp(a, b), Exp(a, Neg(c)))),
                     domain=Complex, conditions=[NotEquals(a, zero)])
diff_in_exp


diff_in_exp_rev = Forall([a, b, c],
                         Equals(Mult(Exp(a, b), Exp(a, Neg(c))),
                                Exp(a, Sub(b, c))),
                         domain=Complex, conditions=[NotEquals(a, zero)])
diff_in_exp_rev

diff_frac_in_exp = Forall([a, b, c, d],
                          Equals(Exp(a, Sub(b, frac(c, d))),
                                 Mult(Exp(a, b), Exp(a, frac(Neg(c), d)))),
                          domain=Complex, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diff_frac_in_exp


diff_frac_in_exp_rev = Forall([a, b, c, d], Equals(Mult(Exp(a, b), Exp(a, frac(Neg(c), d))), Exp(
    a, Sub(b, frac(c, d)))), domain=Complex, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diff_frac_in_exp_rev

# works because log[a^c b^c] = c log a + c log b
exp_of_positives_prod = Forall(c, Forall((a, b),
                                         Equals(Exp(Mult(a, b), c),
                                                Mult(Exp(a, c), Exp(b, c))),
                                         domain=RealPos),
                               domain=Complex)
exp_of_positives_prod

exp_of_positives_prod_rev = Forall(c, Forall((a, b),
                                             Equals(Mult(Exp(a, c), Exp(b, c)),
                                                    Exp(Mult(a, b), c)),
                                             domain=RealPos),
                                   domain=Complex)
exp_of_positives_prod_rev

# Works for integers powers by the commutivity of complex numbers (or their inverses when n < 0).
# Does not work for fractional powers.  Consider sqrt(-1)*sqrt(-1) = -1
# not sqrt((-1)*(-1)) = 1.
int_exp_of_prod = Forall(n, Forall((a, b), Equals(Exp(Mult(a, b), n), Mult(Exp(a, n), Exp(
    b, n))), domain=Complex, conditions=[NotEquals(a, zero), NotEquals(b, zero)]), domain=Integer)
int_exp_of_prod


int_exp_of_prod_rev = Forall(
    n, Forall(
        (a, b), Equals(
            Mult(
                Exp(
                    a, n), Exp(
                        b, n)), Exp(
                            Mult(
                                a, b), n)), domain=Complex, conditions=[
                                    NotEquals(
                                        a, zero), NotEquals(
                                            b, zero)]), domain=Integer)
int_exp_of_prod_rev

nats_pos_exp_of_prod = Forall(n, Forall((a, b),
                                        Equals(Exp(Mult(a, b), n),
                                               Mult(Exp(a, n), Exp(b, n))),
                                        domain=Complex),
                              domain=NaturalPos)
nats_pos_exp_of_prod

nats_pos_exp_of_prod_rev = Forall(n, Forall((a, b),
                                            Equals(Mult(Exp(a, n), Exp(b, n)),
                                                   Exp(Mult(a, b), n)),
                                            domain=Complex),
                                  domain=NaturalPos)
nats_pos_exp_of_prod_rev

# Works for integers powers through repetition of a^b (or a^{-b}) and adding exponents.
# Does not work for fractional powers.  Consider sqrt[(-1)^2] = 1 not
# (-1)^{2*(1/2)} = -1.
int_exp_of_exp = Forall(n, Forall((a, b),
                                  Equals(Exp(Exp(a, b), n),
                                         Exp(a, Mult(b, n))),
                                  domain=Complex, conditions=[NotEquals(a, zero)]),
                        domain=Integer)
int_exp_of_exp

int_exp_of_neg_exp = Forall(n, Forall((a, b),
                                      Equals(Exp(Exp(a, Neg(b)), n),
                                             Exp(a, Neg(Mult(b, n)))),
                                      domain=Complex, conditions=[NotEquals(a, zero)]),
                            domain=Integer)
int_exp_of_neg_exp

neg_int_exp_of_exp = Forall(n, Forall((a, b),
                                      Equals(Exp(Exp(a, b), Neg(n)),
                                             Exp(a, Neg(Mult(b, n)))),
                                      domain=Complex, conditions=[NotEquals(a, zero)]),
                            domain=Integer)

neg_int_exp_of_exp

neg_int_exp_of_neg_exp = Forall(n, Forall((a, b),
                                          Equals(Exp(Exp(a, Neg(b)), Neg(n)),
                                                 Exp(a, Mult(b, n))),
                                          domain=Complex, conditions=[NotEquals(a, zero)]),
                                domain=Integer)

neg_int_exp_of_neg_exp

diff_square_comm = Forall([a, b],
                          Equals(
    Exp(Sub(a, b), two),
    Exp(Sub(b, a), two)),
    domain=Complex)
diff_square_comm

one_exp = Forall([x],
                 Equals(Exp(x, one),
                        x),
                 domain=Complex)
one_exp

exp_one = Forall([x],
                 Equals(Exp(one, x),
                        one),
                 domain=Complex)
exp_one

same_exp_distribute = Forall([x, y, z],
                             Equals(Mult(Exp(x, y), Exp(z, y)),
                                    Exp(Mult(x, z), y)),
                             domain=Complex)
same_exp_distribute

sqrt_of_prod = Forall(x_etc, Equals(sqrt(Mult(x_etc)),
                                    Mult(Etcetera(sqrt(x_multi)))),
                      domain=RealPos)
sqrt_of_prod

prod_of_sqrts = Forall(x_etc, Equals(Mult(Etcetera(sqrt(x_multi))),
                                     sqrt(Mult(x_etc))),
                       domain=RealPos)
prod_of_sqrts

sqrt_times_itself = Forall(
    x,
    Equals(
        Mult(
            sqrt(x),
            sqrt(x)),
        x),
    domain=Real,
    conditions=[
        GreaterThanEquals(
            x,
            zero)])
sqrt_times_itself

end_theorems(locals(), __package__)
