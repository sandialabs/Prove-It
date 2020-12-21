from proveit.logic import Forall, InSet, Equals
from proveit.numbers import Integer, Natural, NaturalPos, Real, RealPos, RealNeg, Complex
from proveit.numbers import Add, GreaterThan, LessThan
from proveit.common import a, b, x, a_etc, c_etc, x_etc, y_etc, z_etc, v_etc, w_etc
from proveit.numbers.common import zero
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

add_int_closure = Forall([x_etc], InSet(Add(x_etc),Integer), domain = Integer)
add_int_closure

add_nat_closure = Forall((a, b), InSet(Add(a, b), Natural), domain=Natural)
add_nat_closure

add_real_closure = Forall([x_etc], InSet(Add(x_etc),Real), domain=Real)
add_real_closure

add_complex_closure = Forall([x_etc], InSet(Add(x_etc),Complex), domain = Complex)
add_complex_closure

add_nat_pos_closure = Forall((a_etc, b, c_etc), InSet(Add(a_etc, b, c_etc), NaturalPos), domain=Natural, conditions=[GreaterThan(b, zero)])
add_nat_pos_closure

add_zero = Forall(x, Equals(Add(zero, x), x), domain=Complex)
add_zero

add_comm = Forall([v_etc,w_etc,x_etc,y_etc,z_etc],
                 Equals(
                        Add(v_etc,w_etc,x_etc,y_etc,z_etc),
                        Add(v_etc,y_etc,x_etc,w_etc,z_etc)
                        ),
                 domain = Complex
                 )
add_comm

add_assoc = Forall([x_etc,y_etc,z_etc],
                  Equals(
                        Add(
                                x_etc,y_etc,z_etc),
                        Add(
                                x_etc,Add(y_etc),z_etc)
                        ),
                  )
add_assoc

add_assoc_rev = Forall([x_etc,y_etc,z_etc],
                  Equals(
                        Add(
                                x_etc,Add(y_etc),z_etc),
                        Add(
                                x_etc,y_etc,z_etc)
                        )
                  )
add_assoc_rev

# One issue with this is that it only applies when |a_etc|+|b_etc| > 0.  This isn't an issue
# for applying the theorem because there will be an error if b is left alone with Add, but
# it will be an issue when deriving this.  Probably need to include |a_etc|+|b_etc| > 0 as a condition.
strictly_increasing_additions = Forall((a_etc, c_etc), Forall(b, GreaterThan(Add(a_etc, b, c_etc), b),
                                                          domain=Real),
                                     domain=RealPos)
strictly_increasing_additions


# In[80]:

# One issue with this is that it only applies when |a_etc|+|b_etc| > 0.  This isn't an issue
# for applying the theorem because there will be an error if b is left alone with Add, but
# it will be an issue when deriving this.  Probably need to include |a_etc|+|b_etc| > 0 as a condition.
strictly_decreasing_additions = Forall((a_etc, c_etc), Forall(b, LessThan(Add(a_etc, b, c_etc), b),
                                                          domain=Real),
                                     domain=RealNeg)
strictly_decreasing_additions



end_theorems(locals(), __package__)
