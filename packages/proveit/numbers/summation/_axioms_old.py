from proveit.logic import Forall, Equals
from proveit.numbers import Sum, Integer, Interval, LessThan, Add, Sub
from proveit.common import a, b, f, x, fa, fb, fx
from proveit.numbers.common import one
from proveit import begin_axioms, end_axioms

begin_axioms(locals())

sum_single = Forall(f, Forall(a,
                              Equals(Sum(x, fx, Interval(a, a)),
                                     fa),
                              domain=Integer))
sum_single

sum_split_last = Forall(f,
                        Forall([a, b],
                               Equals(Sum(x, fx, Interval(a, b)),
                                      Add(Sum(x, fx, Interval(a, Sub(b, one))),
                                          fb)),
                               domain=Integer, conditions=[LessThan(a, b)]))
sum_split_last


end_axioms(locals(), __package__)
