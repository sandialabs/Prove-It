from proveit.logic import Forall, Or, Equals, Implies
from proveit.numbers import Real
from proveit.numbers import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from proveit.common import x, y, z
from proveit import begin_axioms, end_axioms

begin_axioms(locals())

less_than_equals_def = Forall([x, y], Or(LessThan(x, y), Equals(
    x, y)), domain=Real, conditions=LessThanEquals(x, y))
less_than_equals_def

greater_than_equals_def = Forall([x, y], Or(GreaterThan(x, y), Equals(
    x, y)), domain=Real, conditions=GreaterThanEquals(x, y))
greater_than_equals_def

reverse_greater_than_equals = Forall(
    (x, y), Implies(
        GreaterThanEquals(
            x, y), LessThanEquals(
                y, x)))
reverse_greater_than_equals

reverse_less_than_equals = Forall(
    (x, y), Implies(
        LessThanEquals(
            x, y), GreaterThanEquals(
                y, x)))
reverse_less_than_equals

reverse_greater_than = Forall(
    (x, y), Implies(
        GreaterThan(
            x, y), LessThan(
                y, x)))
reverse_greater_than

reverse_less_than = Forall((x, y), Implies(LessThan(x, y), GreaterThan(y, x)))
reverse_less_than

greater_than_equals_def = Forall(
    (x, y), Implies(
        GreaterThanEquals(
            x, y), Or(
                GreaterThan(
                    x, y), Equals(
                        x, y))))
greater_than_equals_def

less_than_equals_def = Forall(
    (x, y), Implies(
        LessThanEquals(
            x, y), Or(
                LessThan(
                    x, y), Equals(
                        x, y))))
less_than_equals_def

less_than_trans_less_than_right = Forall((x, y, z),
                                         Implies(LessThan(x, y),
                                                 Implies(LessThan(y, z),
                                                         LessThan(x, z))))
less_than_trans_less_than_right

less_than_trans_less_than_equals_right = Forall(
    (x, y, z), Implies(
        LessThan(
            x, y), Implies(
                LessThanEquals(
                    y, z), LessThan(
                        x, z))))
less_than_trans_less_than_equals_right

less_than_trans_less_than_left = Forall((x, y, z),
                                        Implies(LessThan(x, y),
                                                Implies(LessThan(z, x),
                                                        LessThan(z, y))))
less_than_trans_less_than_left

less_than_trans_less_than_equals_left = Forall(
    (x, y, z), Implies(
        LessThan(
            x, y), Implies(
                LessThanEquals(
                    z, x), LessThan(
                        z, y))))
less_than_trans_less_than_equals_left

less_than_equals_trans_less_than_right = Forall(
    (x, y, z), Implies(
        LessThanEquals(
            x, y), Implies(
                LessThan(
                    y, z), LessThan(
                        x, z))))
less_than_equals_trans_less_than_right

less_than_equals_trans_less_than_equals_right = Forall(
    (x, y, z), Implies(
        LessThanEquals(
            x, y), Implies(
                LessThanEquals(
                    y, z), LessThanEquals(
                        x, z))))
less_than_equals_trans_less_than_equals_right

less_than_equals_trans_less_than_left = Forall(
    (x, y, z), Implies(
        LessThanEquals(
            x, y), Implies(
                LessThan(
                    z, x), LessThan(
                        z, y))))
less_than_equals_trans_less_than_left

less_than_equals_trans_less_than_equals_left = Forall(
    (x, y, z), Implies(
        LessThanEquals(
            x, y), Implies(
                LessThanEquals(
                    z, x), LessThanEquals(
                        z, y))))
less_than_equals_trans_less_than_equals_left

greater_than_trans_greater_than_right = Forall(
    (x, y, z), Implies(
        GreaterThan(
            x, y), Implies(
                GreaterThan(
                    y, z), GreaterThan(
                        x, z))))
greater_than_trans_greater_than_right

greater_than_trans_greater_than_equals_right = Forall(
    (x, y, z), Implies(
        GreaterThan(
            x, y), Implies(
                GreaterThanEquals(
                    y, z), GreaterThan(
                        x, z))))
greater_than_trans_greater_than_equals_right

greater_than_trans_greater_than_left = Forall(
    (x, y, z), Implies(
        GreaterThan(
            x, y), Implies(
                GreaterThan(
                    z, x), GreaterThan(
                        z, y))))
greater_than_trans_greater_than_left

greater_than_trans_greater_than_equals_left = Forall(
    (x, y, z), Implies(
        GreaterThan(
            x, y), Implies(
                GreaterThanEquals(
                    z, x), GreaterThan(
                        z, y))))
greater_than_trans_greater_than_equals_left


greater_than_equals_trans_greater_than_right = Forall(
    (x, y, z), Implies(
        GreaterThanEquals(
            x, y), Implies(
                GreaterThan(
                    y, z), GreaterThan(
                        x, z))))
greater_than_equals_trans_greater_than_right


greater_than_equals_trans_greater_than_equals_right = Forall(
    (x, y, z), Implies(
        GreaterThanEquals(
            x, y), Implies(
                GreaterThanEquals(
                    y, z), GreaterThanEquals(
                        x, z))))
greater_than_equals_trans_greater_than_equals_right


greater_than_equals_trans_greater_than_left = Forall(
    (x, y, z), Implies(
        GreaterThanEquals(
            x, y), Implies(
                GreaterThan(
                    z, x), GreaterThan(
                        z, y))))
greater_than_equals_trans_greater_than_left

greater_than_equals_trans_greater_than_equals_left = Forall(
    (x, y, z), Implies(
        GreaterThanEquals(
            x, y), Implies(
                GreaterThanEquals(
                    z, x), GreaterThanEquals(
                        z, y))))
greater_than_equals_trans_greater_than_equals_left


end_axioms(locals(), __package__)
