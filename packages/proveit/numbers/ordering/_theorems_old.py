from proveit.logic import Forall, Implies, InSet, NotEquals, And, Or, Boolean
from proveit.numbers import Integer, Real, RealPos
from proveit.numbers import GreaterThan, GreaterThanEquals, LessThan, LessThanEquals, Min, Max, Add, Sub, Neg, Mult, frac
from proveit.common import a, b, c, d, x
from proveit.numbers.common import zero, one
from proveit import begin_theorems, end_theorems

begin_theorems(locals())

min_real_closure = Forall((a, b), InSet(Min(a, b), Real), domain=Real)
min_real_closure

min_real_pos_closure = Forall(
    (a, b), InSet(Min(a, b), RealPos), domain=RealPos)
min_real_pos_closure

max_real_closure = Forall((a, b), InSet(Max(a, b), Real), domain=Real)
max_real_closure

max_real_pos_closure = Forall(
    (a, b), InSet(Max(a, b), RealPos), domain=RealPos)
max_real_pos_closure

relax_greater_than = Forall([a, b],
                            GreaterThanEquals(a, b),
                            domain=Real,
                            conditions=GreaterThan(a, b))
relax_greater_than

relax_less_than = Forall([a, b],
                         LessThanEquals(a, b),
                         domain=Real,
                         conditions=LessThan(a, b))
relax_less_than

less_than_is_bool = Forall([a, b], InSet(LessThan(a, b), Boolean), domain=Real)
less_than_is_bool

less_than_equals_is_bool = Forall([a, b], InSet(
    LessThanEquals(a, b), Boolean), domain=Real)
less_than_equals_is_bool

greater_than_is_bool = Forall([a, b], InSet(
    GreaterThan(a, b), Boolean), domain=Real)
greater_than_is_bool

greater_than_equals_is_bool = Forall([a, b], InSet(
    GreaterThanEquals(a, b), Boolean), domain=Real)
greater_than_equals_is_bool

not_equals_is_less_than_or_greater_than = Forall(
    (a, x), Or(
        LessThan(
            x, a), GreaterThan(
                x, a)), domain=Real, conditions=[
                    NotEquals(
                        x, a)])
not_equals_is_less_than_or_greater_than

shift_less_than_to_less_than_equals = Forall((a, b), LessThanEquals(
    a, b), domain=Integer, conditions=[LessThan(Sub(a, one), b)])
shift_less_than_to_less_than_equals

less_than_equals_add_right = Forall([a, b, c], LessThanEquals(
    Add(a, c), Add(b, c)), domain=Real, conditions=[LessThanEquals(a, b)])
less_than_equals_add_right

less_than_equals_add_left = Forall([a, b, c], LessThanEquals(
    Add(c, a), Add(c, b)), domain=Real, conditions=[LessThanEquals(a, b)])
less_than_equals_add_left

less_than_equals_subtract = Forall([a, b, c], LessThanEquals(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[LessThanEquals(a, b)])
less_than_equals_subtract

less_than_add_right = Forall([a, b, c], LessThan(
    Add(a, c), Add(b, c)), domain=Real, conditions=[LessThan(a, b)])
less_than_add_right

less_than_add_left = Forall([a, b, c], LessThan(
    Add(c, a), Add(c, b)), domain=Real, conditions=[LessThan(a, b)])
less_than_add_left

less_than_subtract = Forall([a, b, c], LessThan(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[LessThan(a, b)])
less_than_subtract

greater_than_equals_add_right = Forall([a, b, c], GreaterThanEquals(
    Add(a, c), Add(b, c)), domain=Real, conditions=[GreaterThanEquals(a, b)])
greater_than_equals_add_right

greater_than_equals_add_left = Forall([a, b, c], GreaterThanEquals(
    Add(c, a), Add(c, b)), domain=Real, conditions=[GreaterThanEquals(a, b)])
greater_than_equals_add_left

greater_than_equals_subtract = Forall([a, b, c], GreaterThanEquals(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[GreaterThanEquals(a, b)])
greater_than_equals_subtract

greater_than_add_right = Forall([a, b, c], GreaterThan(
    Add(a, c), Add(b, c)), domain=Real, conditions=[GreaterThan(a, b)])
greater_than_add_right

greater_than_add_left = Forall([a, b, c], GreaterThan(
    Add(c, a), Add(c, b)), domain=Real, conditions=[GreaterThan(a, b)])
greater_than_add_left

greater_than_subtract = Forall([a, b, c], GreaterThan(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[GreaterThan(a, b)])
greater_than_subtract

negated_less_than = Forall([a, b], GreaterThan(
    Neg(a), Neg(b)), domain=Real, conditions=[LessThan(a, b)])
negated_less_than

negated_less_than_equals = Forall([a, b], GreaterThanEquals(
    Neg(a), Neg(b)), domain=Real, conditions=[LessThanEquals(a, b)])
negated_less_than_equals

negated_greater_than = Forall([a, b], LessThan(
    Neg(a), Neg(b)), domain=Real, conditions=[GreaterThan(a, b)])
negated_greater_than

negated_greater_than_equals = Forall([a, b], LessThanEquals(
    Neg(a), Neg(b)), domain=Real, conditions=[GreaterThanEquals(a, b)])
negated_greater_than_equals

end_theorems(locals(), __package__)
