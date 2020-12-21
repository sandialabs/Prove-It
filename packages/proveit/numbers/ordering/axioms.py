from proveit.logic import Forall, Or, Equals, Implies
from proveit.numbers import Real
from proveit.numbers import Less, LessEq, Greater, GreaterEq
from proveit.common import x, y, z
from proveit import begin_axioms, end_axioms

begin_axioms(locals())

less_than_equals_def = Forall([x, y], Or(Less(x, y), Equals(x, y)), domain=Real, conditions=LessEq(x, y))
less_than_equals_def

greater_than_equals_def = Forall([x, y], Or(Greater(x, y), Equals(x, y)), domain=Real, conditions=GreaterEq(x, y))
greater_than_equals_def

reverse_greater_than_equals = Forall((x, y), Implies(GreaterEq(x, y), LessEq(y, x)))
reverse_greater_than_equals

reverse_less_than_equals = Forall((x, y), Implies(LessEq(x, y), GreaterEq(y, x)))
reverse_less_than_equals

reverse_greater_than = Forall((x, y), Implies(Greater(x, y), Less(y, x)))
reverse_greater_than

reverse_less_than = Forall((x, y), Implies(Less(x, y), Greater(y, x)))
reverse_less_than

greater_than_equals_def = Forall((x,y), Implies(GreaterEq(x,y), Or(Greater(x,y),Equals(x,y))))
greater_than_equals_def

less_than_equals_def = Forall((x,y), Implies(LessEq(x,y), Or(Less(x,y),Equals(x,y))))
less_than_equals_def

less_than_trans_less_than_right = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(Less(y,z),
                                             Less(x,z))))
less_than_trans_less_than_right

less_than_trans_less_than_equals_right = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(LessEq(y,z),
                                             Less(x,z))))
less_than_trans_less_than_equals_right

less_than_trans_less_than_left = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(Less(z,x),
                                             Less(z,y))))
less_than_trans_less_than_left

less_than_trans_less_than_equals_left = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(LessEq(z,x),
                                             Less(z,y))))
less_than_trans_less_than_equals_left

less_than_equals_trans_less_than_right = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(Less(y,z),
                                             Less(x,z))))
less_than_equals_trans_less_than_right

less_than_equals_trans_less_than_equals_right = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(LessEq(y,z),
                                             LessEq(x,z))))
less_than_equals_trans_less_than_equals_right

less_than_equals_trans_less_than_left = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(Less(z,x),
                                             Less(z,y))))
less_than_equals_trans_less_than_left

less_than_equals_trans_less_than_equals_left = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(LessEq(z,x),
                                             LessEq(z,y))))
less_than_equals_trans_less_than_equals_left

greater_than_trans_greater_than_right = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(Greater(y,z),
                                                  Greater(x,z))))
greater_than_trans_greater_than_right

greater_than_trans_greater_than_equals_right = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(GreaterEq(y,z),
                                                  Greater(x,z))))
greater_than_trans_greater_than_equals_right

greater_than_trans_greater_than_left = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(Greater(z,x),
                                                  Greater(z,y))))
greater_than_trans_greater_than_left

greater_than_trans_greater_than_equals_left = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(GreaterEq(z,x),
                                                  Greater(z,y))))
greater_than_trans_greater_than_equals_left


greater_than_equals_trans_greater_than_right = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(Greater(y,z),
                                                             Greater(x,z))))
greater_than_equals_trans_greater_than_right


greater_than_equals_trans_greater_than_equals_right = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(GreaterEq(y,z),
                                                             GreaterEq(x,z))))
greater_than_equals_trans_greater_than_equals_right


greater_than_equals_trans_greater_than_left = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(Greater(z,x),
                                                             Greater(z,y))))
greater_than_equals_trans_greater_than_left

greater_than_equals_trans_greater_than_equals_left = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(GreaterEq(z,x),
                                                             GreaterEq(z,y))))
greater_than_equals_trans_greater_than_equals_left


end_axioms(locals(), __package__)
