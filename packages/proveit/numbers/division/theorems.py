from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Implies
from proveit.numbers import Integer, NaturalPos, Real, RealPos, Complex
from proveit.numbers import Divide, frac, Add, Sub, Sum, Mult, Exp
from proveit.common import a, b, c, n, w, x, y, z, P, S, x_multi, w_etc, x_etc, y_etc, z_etc, Py_etc
from proveit.numbers.common import zero, one, ComplexSansZero
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

divide_real_closure = Forall([a, b], InSet(Divide(a, b), Real), domain=Real, conditions=[NotEquals(b, zero)])
divide_real_closure       

divide_real_pos_closure = Forall([a, b], InSet(Divide(a, b), RealPos), domain=RealPos, conditions=[NotEquals(b, zero)])
divide_real_pos_closure

fraction_real_closure = Forall([a, b], InSet(frac(a, b), Real), domain=Real, conditions=[NotEquals(b, zero)])
fraction_real_closure   

fraction_pos_closure = Forall([a, b], InSet(frac(a, b), RealPos), domain=RealPos, conditions=[NotEquals(b, zero)])
fraction_pos_closure

divide_complex_closure = Forall([a, b], InSet(Divide(a, b), Complex), domain=Complex, conditions=[NotEquals(b, zero)])
divide_complex_closure       

fraction_complex_closure = Forall([a, b], InSet(frac(a, b), Complex), domain=Complex, conditions=[NotEquals(b, zero)])
fraction_complex_closure          

divide_not_eq_zero = Forall([a, b], NotEquals(Divide(a,b), zero), domain=ComplexSansZero)
divide_not_eq_zero

fraction_not_eq_zero = Forall([a, b], NotEquals(frac(a,b), zero), domain=ComplexSansZero)
fraction_not_eq_zero

frac_zero_numer = Forall(x, Equals(frac(zero, x), zero), domain=Complex)
frac_zero_numer

frac_one_denom = Forall(x, Equals(frac(x, one), x), domain=Complex)
frac_one_denom

distributefrac_through_sum = Forall([x_etc, y], 
                                      Equals(frac(Add(x_etc), y),
                                             Add(Etcetera(frac(x_multi, y)))), 
                                      domain=Complex, conditions=[NotEquals(y, zero)])
distributefrac_through_sum

distributefrac_through_sum_rev = Forall([x_etc, y], 
                                      Equals(Add(Etcetera(frac(x_multi, y))),
                                             frac(Add(x_etc), y)), 
                                      domain=Complex, conditions=[NotEquals(y, zero)])
distributefrac_through_sum_rev

distributefrac_through_subtract = Forall([x, y, z], 
                                          Equals(frac(Sub(x, y), z),
                                                 Sub(frac(x, z), frac(y, z))), 
                                          domain=Complex, conditions=[NotEquals(z, zero)])
distributefrac_through_subtract

distributefrac_through_subtract_rev = Forall([x, y, z], 
                                              Equals(Sub(frac(x, z), frac(y, z)),
                                                     frac(Sub(x, y), z)), 
                                              domain=Complex, conditions=[NotEquals(z, zero)])
distributefrac_through_subtract_rev

distributefrac_through_summation = Forall([P, S],
                                    Implies(Forall(y_etc, InSet(Py_etc, Complex), domain=S),
                                            Forall(z,
                                                   Equals(frac(Sum(y_etc, Py_etc, domain=S), z),
                                                          Sum(y_etc, frac(Py_etc, z), domain=S)),
                                                  domain=Complex)))
distributefrac_through_summation

distributefrac_through_summation_rev = Forall([P, S],
                                    Implies(Forall(y_etc, InSet(Py_etc, Complex), domain=S),
                                            Forall(z,
                                                   Equals(Sum(y_etc, frac(Py_etc, z), domain=S),
                                                         frac(Sum(y_etc, Py_etc, domain=S), z)),
                                                  domain=Complex)))
distributefrac_through_summation_rev

frac_in_prod = Forall([w_etc, x, y, z_etc], Equals(Mult(w_etc, frac(x, y), z_etc),
                                        frac(Mult(w_etc, x, z_etc), y)), domain=Complex)
frac_in_prod

frac_in_prod_rev = Forall([w_etc, x, y, z_etc], 
                       Equals(frac(Mult(w_etc, x, z_etc), y),
                             Mult(w_etc, frac(x, y), z_etc)), domain=Complex)
frac_in_prod_rev

prod_of_fracs = Forall([x, y, z, w], Equals(Mult(frac(x, z), frac(y, w)),
                                           frac(Mult(x, y), Mult(z, w))), domain=Complex)
prod_of_fracs

prod_of_fracs_rev = Forall([x, y, z, w], Equals(frac(Mult(x, y), Mult(z, w)),
                                          Mult(frac(x, z), frac(y, w))), domain=Complex)
prod_of_fracs_rev

prod_of_fracs_left_numer_one = Forall([x, y, z], Equals(Mult(frac(one, y), frac(x, z)),
                                                 frac(x, Mult(y, z))), domain=Complex)
prod_of_fracs_left_numer_one

prod_of_fracs_left_numer_one_rev = Forall([x, y, z], Equals(frac(x, Mult(y, z)),
                                                   Mult(frac(one, y), frac(x, z))), domain=Complex)
prod_of_fracs_left_numer_one_rev

prod_of_fracs_right_numer_one = Forall([x, y, z], Equals(Mult(frac(x, y), frac(one, z)),
                                                 frac(x, Mult(y, z))), domain=Complex)
prod_of_fracs_right_numer_one

prod_of_fracs_right_numer_one_rev = Forall([x, y, z], Equals(frac(x, Mult(y, z)),
                                                    Mult(frac(x, y), frac(one, z))), domain=Complex)
prod_of_fracs_right_numer_one_rev

frac_cancel_left = Forall([x,y,z],
                   Equals(frac(Mult(x,y),Mult(x,z)),
                         frac(y,z)),domain=Complex, conditions=[NotEquals(x, zero)])
frac_cancel_left

frac_cancel_denom_left = Forall([x,y],
                             Equals(frac(Mult(x,y),x),
                                    y),domain=Complex, conditions=[NotEquals(x, zero)])
frac_cancel_denom_left

frac_cancel_numer_left = Forall([x,y],
                             Equals(frac(x,Mult(x,y)),
                                    frac(one,y)),domain=Complex, conditions=[NotEquals(x, zero)])
frac_cancel_numer_left

mult_frac_left_cancel = Forall([x,y],
                      Equals(Mult(frac(x,y),y),x),
                      domain = Complex, conditions = [NotEquals(y, zero)])
mult_frac_left_cancel

mult_frac_right_cancel = Forall([x,y],
                             Equals(Mult(x, frac(y, x)),y),
                             domain = Complex, conditions = [NotEquals(x, zero)])
mult_frac_right_cancel

frac_cancel_complete = Forall(x, Equals(frac(x, x), one), 
                            domain=Complex, conditions = [NotEquals(x, zero)])
frac_cancel_complete

reversefrac_of_subtractions = Forall([w, x, y, z], Equals(frac(Sub(w, x), Sub(y, z)),
                                                           frac(Sub(x, w), Sub(z, y))), domain=Complex)
reversefrac_of_subtractions

frac_int_exp = Forall(n, Forall((a, b), 
                              Equals(frac(Exp(a, n), Exp(b, n)),
                                     Exp(frac(a, b), n)),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integer)
frac_int_exp

frac_int_exp_rev = Forall(n, Forall((a, b), 
                                 Equals(Exp(frac(a, b), n),
                                        frac(Exp(a, n), Exp(b, n))),
                             conditions = [NotEquals(a, zero), NotEquals(b, zero)]),
                    domain=Integer)
frac_int_exp_rev

frac_nat_pos_exp = Forall(n, Forall((a, b), 
                              Equals(frac(Exp(a, n), Exp(b, n)),
                                     Exp(frac(a, b), n)),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalPos)
frac_nat_pos_exp

frac_nat_pos_exp_rev = Forall(n, Forall((a, b), 
                              Equals(Exp(frac(a, b), n),
                                     frac(Exp(a, n), Exp(b, n))),
                             conditions = [NotEquals(b, zero)]),
                    domain=NaturalPos)
frac_nat_pos_exp_rev

end_theorems(locals(), __package__)
