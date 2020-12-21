from proveit.logic import Forall, Implies, InSet, NotEquals, And, Or, Boolean
from proveit.numbers import Integer, Real, RealPos
from proveit.numbers import Greater, GreaterEq, Less, LessEq, Min, Max, Add, Sub, Neg, Mult, frac
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
                            GreaterEq(a, b),
                            domain=Real,
                            conditions=Greater(a, b))
relax_greater_than

relax_less_than = Forall([a, b],
                         LessEq(a, b),
                         domain=Real,
                         conditions=Less(a, b))
relax_less_than

less_than_is_bool = Forall([a, b], InSet(Less(a, b), Boolean), domain=Real)
less_than_is_bool

less_than_equals_is_bool = Forall(
    [a, b], InSet(LessEq(a, b), Boolean), domain=Real)
less_than_equals_is_bool

greater_than_is_bool = Forall([a, b], InSet(
    Greater(a, b), Boolean), domain=Real)
greater_than_is_bool

greater_than_equals_is_bool = Forall(
    [a, b], InSet(GreaterEq(a, b), Boolean), domain=Real)
greater_than_equals_is_bool

not_equals_is_less_than_or_greater_than = Forall(
    (a, x), Or(
        Less(
            x, a), Greater(
                x, a)), domain=Real, conditions=[
                    NotEquals(
                        x, a)])
not_equals_is_less_than_or_greater_than

shift_less_than_to_less_than_equals = Forall((a, b), LessEq(
    a, b), domain=Integer, conditions=[Less(Sub(a, one), b)])
shift_less_than_to_less_than_equals

less_than_equals_add_right = Forall([a, b, c], LessEq(
    Add(a, c), Add(b, c)), domain=Real, conditions=[LessEq(a, b)])
less_than_equals_add_right

less_than_equals_add_left = Forall([a, b, c], LessEq(
    Add(c, a), Add(c, b)), domain=Real, conditions=[LessEq(a, b)])
less_than_equals_add_left

less_than_equals_subtract = Forall([a, b, c], LessEq(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[LessEq(a, b)])
less_than_equals_subtract

less_than_add_right = Forall([a, b, c], Less(
    Add(a, c), Add(b, c)), domain=Real, conditions=[Less(a, b)])
less_than_add_right

less_than_add_left = Forall([a, b, c], Less(
    Add(c, a), Add(c, b)), domain=Real, conditions=[Less(a, b)])
less_than_add_left

less_than_subtract = Forall([a, b, c], Less(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[Less(a, b)])
less_than_subtract

greater_than_equals_add_right = Forall([a, b, c], GreaterEq(
    Add(a, c), Add(b, c)), domain=Real, conditions=[GreaterEq(a, b)])
greater_than_equals_add_right

greater_than_equals_add_left = Forall([a, b, c], GreaterEq(
    Add(c, a), Add(c, b)), domain=Real, conditions=[GreaterEq(a, b)])
greater_than_equals_add_left

greater_than_equals_subtract = Forall([a, b, c], GreaterEq(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[GreaterEq(a, b)])
greater_than_equals_subtract

greater_than_add_right = Forall([a, b, c], Greater(
    Add(a, c), Add(b, c)), domain=Real, conditions=[Greater(a, b)])
greater_than_add_right

greater_than_add_left = Forall([a, b, c], Greater(
    Add(c, a), Add(c, b)), domain=Real, conditions=[Greater(a, b)])
greater_than_add_left

greater_than_subtract = Forall([a, b, c], Greater(
    Sub(a, c), Sub(b, c)), domain=Real, conditions=[Greater(a, b)])
greater_than_subtract

negated_less_than = Forall([a, b], Greater(
    Neg(a), Neg(b)), domain=Real, conditions=[Less(a, b)])
negated_less_than

negated_less_than_equals = Forall([a, b], GreaterEq(
    Neg(a), Neg(b)), domain=Real, conditions=[LessEq(a, b)])
negated_less_than_equals

negated_greater_than = Forall([a, b], Less(
    Neg(a), Neg(b)), domain=Real, conditions=[Greater(a, b)])
negated_greater_than

negated_greater_than_equals = Forall([a, b], LessEq(
    Neg(a), Neg(b)), domain=Real, conditions=[GreaterEq(a, b)])
negated_greater_than_equals

end_theorems(locals(), __package__)
