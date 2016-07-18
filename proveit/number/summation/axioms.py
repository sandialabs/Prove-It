from proveit.logic import Forall, Equals
from proveit.number import Sum, Integers, Interval, LessThan, Add, Sub
from proveit.common import a, b, f, x, fa, fb, fx
from proveit.number.common import one
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

sumSingle = Forall(f, Forall(a,
                              Equals(Sum(x,fx,Interval(a,a)),
                                     fa),
                              domain=Integers))
sumSingle

sumSplitLast = Forall(f, 
                      Forall([a,b],
                             Equals(Sum(x,fx,Interval(a,b)),
                                    Add(Sum(x,fx,Interval(a,Sub(b, one))),
                                       fb)),
                             domain=Integers, conditions=[LessThan(a, b)]))
sumSplitLast


endAxioms(locals(), __package__)
