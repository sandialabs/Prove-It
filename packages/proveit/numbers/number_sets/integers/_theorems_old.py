from proveit import Operation
from proveit.logic import Forall, InSet, NotInSet, NotEquals, And, Implies, Equals, Boolean
from proveit.numbers import Integer, Natural, NaturalPos, Interval, Real, RealPos, Complex
from proveit.numbers import Add, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals
from proveit.numbers import Len
from proveit.common import a, b, n, m, x, y, P, S, x_multi, x_etc, Px_etc
from proveit.numbers import zero, one, two, three, four, five, six, seven, eight, nine
from proveit.numbers.common import Pzero, Pm, P_mAddOne, Pn
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

zero_in_nats = InSet(zero, Natural)

successive_nats = Forall(n, InSet(Add(n, one), Natural), domain=Natural)

induction_lemma = Forall(n, Forall(S, Implies(And(InSet(zero, S), Forall(x, InSet(Add(x,one), S), domain=S)), InSet(n, S))), domain=Natural)

induction = Forall(P, Implies(And(Pzero, Forall(m, P_mAddOne, domain=Natural, conditions=[Pm])), Forall(n, Pn, Natural)))

zero_len_expr_tuple = Equals(Len(), zero)

multi_var_induction = Forall(P, Implies(Forall((x_multi, y), Implies(Px_etc, Operation(P, [x_etc, y]))), Forall(x_multi, Px_etc)))

in_ints_is_bool = Forall(a, InSet(InSet(a, Integer), Boolean))
in_ints_is_bool

not_in_ints_is_bool = Forall(a, InSet(NotInSet(a, Integer), Boolean))
not_in_ints_is_bool

int_within_real = Forall(a, InSet(a, Real), domain=Integer)
int_within_real

int_within_complex = Forall(a, InSet(a, Complex), domain=Integer)
int_within_complex

in_natural_if_non_neg = Forall(a, InSet(a,Natural), domain=Integer, conditions=[GreaterThanEquals(a, zero)])
in_natural_if_non_neg

in_natural_pos_if_pos = Forall(a, InSet(a,NaturalPos), domain=Integer, conditions=[GreaterThan(a, zero)])
in_natural_pos_if_pos

interval_is_int = Forall((a, b), Forall(n, InSet(n, Integer), domain=Interval(a, b)), domain=Integer)
interval_is_int          

interval_is_nat = Forall((a, b), Forall(n, InSet(n, Natural), domain=Interval(a, b)), domain=Natural)
interval_is_nat  

interval_in_nat_pos = Forall((a, b), Forall(n, InSet(n, NaturalPos), domain=Interval(a, b)), domain=Integer, conditions=[GreaterThan(a, zero)])
interval_in_nat_pos

all_in_negative_interval_are_negative = Forall((a, b), Forall(n, LessThan(n, zero), domain=Interval(a, b)), domain=Integer, conditions=[LessThan(b, zero)])
all_in_negative_interval_are_negative

all_in_positive_interval_are_positive = Forall((a, b), Forall(n, GreaterThan(n, zero), domain=Interval(a, b)), domain=Integer, conditions=[GreaterThan(a, zero)])
all_in_positive_interval_are_positive

interval_lower_bound = Forall((a, b), Forall(n, LessThanEquals(a, n), domain=Interval(a, b)), domain=Integer)
interval_lower_bound

interval_upper_bound = Forall((a, b), Forall(n, LessThanEquals(n, b), domain=Interval(a, b)), domain=Integer)
interval_upper_bound

in_interval = Forall((a, b, n), InSet(n, Interval(a, b)), domain=Integer, conditions=[LessThanEquals(a, n), LessThanEquals(n, b)])
in_interval

nat_within_int = Forall(a,InSet(a,Integer),domain = Natural)
nat_within_int

nat_within_real = Forall(a,InSet(a,Real),domain = Natural)
nat_within_real

nat_within_complex = Forall(a,InSet(a,Complex),domain = Natural)
nat_within_complex

nats_pos_in_natural = Forall(a,InSet(a,Natural),domain = NaturalPos)
nats_pos_in_natural

nats_pos_in_integer = Forall(a,InSet(a,Integer),domain = NaturalPos)
nats_pos_in_integer

nat_pos_within_real_pos = Forall(a,InSet(a,RealPos),domain = NaturalPos)
nat_pos_within_real_pos

nat_pos_within_real = Forall(a,InSet(a,Real),domain = NaturalPos)
nat_pos_within_real

nat_pos_within_complex = Forall(a,InSet(a,Complex),domain = NaturalPos)
nat_pos_within_complex

natural_lower_bound = Forall(n, GreaterThanEquals(n, zero), domain=Natural)
natural_lower_bound

natural_pos_lower_bound = Forall(n, GreaterThanEquals(n, one), domain=NaturalPos)
natural_pos_lower_bound

one_in_natural = InSet(one,Natural)
one_in_natural

two_in_natural = InSet(two,Natural)
two_in_natural

three_in_natural = InSet(three,Natural)
three_in_natural

four_in_natural = InSet(four,Natural)
four_in_natural

five_in_natural = InSet(five,Natural)
five_in_natural

six_in_natural = InSet(six,Natural)
six_in_natural

seven_in_natural = InSet(seven,Natural)
seven_in_natural

eight_in_natural = InSet(eight,Natural)
eight_in_natural

nine_in_natural = InSet(nine,Natural)
nine_in_natural

one_not_zero = NotEquals(one, zero)
one_not_zero

two_not_zero = NotEquals(two, zero)
two_not_zero

three_not_zero = NotEquals(three, zero)
three_not_zero

four_not_zero = NotEquals(four, zero)
four_not_zero

five_not_zero = NotEquals(five, zero)
five_not_zero

six_not_zero = NotEquals(six, zero)
six_not_zero

seven_not_zero = NotEquals(seven, zero)
seven_not_zero

eight_not_zero = NotEquals(eight, zero)
eight_not_zero

nine_not_zero = NotEquals(nine, zero)
nine_not_zero

one_is_positive = GreaterThan(one,zero)
one_is_positive

two_is_positive = GreaterThan(two,zero)
two_is_positive

three_is_positive = GreaterThan(three,zero)
three_is_positive

four_is_positive = GreaterThan(four,zero)
four_is_positive

five_is_positive = GreaterThan(five,zero)
five_is_positive

six_is_positive = GreaterThan(six,zero)
six_is_positive

seven_is_positive = GreaterThan(seven,zero)
seven_is_positive

eight_is_positive = GreaterThan(eight,zero)
eight_is_positive

nine_is_positive = GreaterThan(nine,zero)
nine_is_positive

one_in_natural_pos = InSet(one, NaturalPos)
one_in_natural_pos

two_in_natural_pos = InSet(two, NaturalPos)
two_in_natural_pos

three_in_natural_pos = InSet(three, NaturalPos)
three_in_natural_pos

four_in_natural_pos = InSet(four, NaturalPos)
four_in_natural_pos

five_in_natural_pos = InSet(five, NaturalPos)
five_in_natural_pos

six_in_natural_pos = InSet(six, NaturalPos)
six_in_natural_pos

seven_in_natural_pos = InSet(seven, NaturalPos)
seven_in_natural_pos

eight_in_natural_pos = InSet(eight, NaturalPos)
eight_in_natural_pos

nine_in_natural_pos = InSet(nine, NaturalPos)
nine_in_natural_pos

naturals_induction = Forall(P, Implies(And(Operation(P, zero), 
                                          Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                 domain=Natural)),
                                      Forall(n, Operation(P, n), domain=Natural)))
naturals_induction      

naturals_pos_induction = Forall(P, Implies(And(Operation(P, one), 
                                             Forall(n, Implies(Operation(P, n), Operation(P, Add(n, one))),
                                                    domain=NaturalPos)),
                                         Forall(n, Operation(P, n), domain=NaturalPos)))
naturals_pos_induction 

end_theorems(locals(), __package__)
