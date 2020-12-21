from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals, Implies
from proveit.numbers import Mult, Natural, NaturalPos, Integer, Real, RealPos, Complex, Add, Sub, Sum
from proveit.common import a, b, x, y, P, S, y_multi, v_etc, w_etc, x_etc, y_etc, z_etc, Py_etc
from proveit.numbers.common import zero, one, ComplexSansZero
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

mult_assoc = Forall([x_etc, y_etc, z_etc],
                    Equals(
    Mult(
        x_etc, y_etc, z_etc),
    Mult(
        x_etc, Mult(y_etc), z_etc)
)
)
mult_assoc

mult_nat_closure = Forall((a, b), InSet(Mult(a, b), Natural), domain=Natural)
mult_nat_closure

mult_nat_pos_closure = Forall((a, b), InSet(
    Mult(a, b), NaturalPos), domain=NaturalPos)
mult_nat_pos_closure

mult_int_closure = Forall([x_etc], InSet(Mult(x_etc), Integer), domain=Integer)
mult_int_closure

mult_real_closure = Forall([x_etc], InSet(Mult(x_etc), Real), domain=Real)
mult_real_closure

mult_real_pos_closure = Forall(
    [x_etc],
    InSet(
        Mult(x_etc),
        RealPos),
    domain=RealPos)
mult_real_pos_closure

mult_complex_closure = Forall(
    [x_etc],
    InSet(
        Mult(x_etc),
        Complex),
    domain=Complex)
mult_complex_closure

mult_not_eq_zero = Forall(
    [x_etc],
    NotEquals(
        Mult(x_etc),
        zero),
    domain=ComplexSansZero)
mult_not_eq_zero

mult_one = Forall(x, Equals(Mult(one, x), x), domain=Complex)
mult_one

mult_zero = Forall(x, Equals(Mult(zero, x), zero), domain=Complex)
mult_zero

mult_comm = Forall([v_etc, w_etc, x_etc, y_etc, z_etc],
                   Equals(
    Mult(v_etc, w_etc, x_etc, y_etc, z_etc),
    Mult(v_etc, y_etc, x_etc, w_etc, z_etc)
),
    domain=Complex
)
mult_comm

mult_assoc_rev = Forall([x_etc, y_etc, z_etc],
                        Equals(
                        Mult(
                            x_etc, Mult(y_etc), z_etc),
                        Mult(
                            x_etc, y_etc, z_etc)
                        )
                        )
mult_assoc_rev

distribute_through_sum = Forall([x_etc, y_etc, z_etc],
                                Equals(
    Mult(x_etc, Add(y_etc), z_etc),
    Add(Etcetera(Mult(x_etc, y_multi, z_etc)))
),
    domain=Complex
)
distribute_through_sum

distribute_through_sum_rev = Forall([x_etc, y_etc, z_etc], Equals(Add(Etcetera(
    Mult(x_etc, y_multi, z_etc))), Mult(x_etc, Add(y_etc), z_etc)), domain=Complex)
distribute_through_sum_rev

distribute_through_subtract = Forall([w_etc, x, y, z_etc],
                                     Equals(
    Mult(w_etc, Sub(x, y), z_etc),
    Sub(Mult(w_etc, x, z_etc), Mult(w_etc, y, z_etc))
),
    domain=Complex
)
distribute_through_subtract

distribute_through_subtract_rev = Forall([w_etc, x, y, z_etc],
                                         Equals(
    Sub(Mult(w_etc, x, z_etc), Mult(w_etc, y, z_etc)),
    Mult(w_etc, Sub(x, y), z_etc)
),
    domain=Complex
)
distribute_through_subtract_rev

distribute_through_summation = Forall([P, S],
                                      Implies(Forall(y_etc, InSet(Py_etc, Complex), domain=S),
                                              Forall([x_etc, z_etc],
                                                     Equals(Mult(x_etc, Sum(y_etc, Py_etc, domain=S), z_etc),
                                                            Sum(y_etc, Mult(x_etc, Py_etc, z_etc), domain=S)),
                                                     domain=Complex)))
distribute_through_summation


distribute_through_summation_rev = Forall([P, S],
                                          Implies(Forall(y_etc, InSet(Py_etc, Complex), domain=S),
                                                  Forall([x_etc, z_etc],
                                                         Equals(Sum(y_etc, Mult(x_etc, Py_etc, z_etc), domain=S),
                                                                Mult(x_etc, Sum(y_etc, Py_etc, domain=S), z_etc)),
                                                         domain=Complex)))
distribute_through_summation_rev

end_theorems(locals(), __package__)
