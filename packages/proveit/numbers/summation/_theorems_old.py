from proveit import Operation
from proveit.logic import Forall, Implies, InSet, Equals, SetOfAll
from proveit.numbers import Integer, Real, Complex
from proveit.numbers import Sum, Interval, Exp, frac, Sub, Add, LessThan, LessThanEquals
from proveit.common import a, b, c, f, g, k, l, m, n, x, y, fa, fx, gx, gy, x_multi, x_etc, P, R, S, Px_etc
from proveit.numbers.common import zero, one, infinity

from proveit import begin_theorems, end_theorems

begin_theorems(locals())

summation_real_closure = Forall([P, S], Implies(Forall(x_multi, InSet(Px_etc, Real), domain=S), 
                                              InSet(Sum(x_multi, Px_etc, domain=S), Real)))
summation_real_closure

summation_complex_closure = Forall([P, S], Implies(Forall(x_multi, InSet(Px_etc, Complex), domain=S), 
                                          InSet(Sum(x_multi, Px_etc, domain=S), Complex)))
summation_complex_closure


sum_split_after = Forall(f, Forall([a,b,c],
                            Equals(Sum(x,fx,Interval(a,c)),
                                   Add(Sum(x,fx,Interval(a,b)),
                                       Sum(x,fx,Interval(Add(b,one),c)))),
                                 domain=Integer, conditions=[LessThanEquals(a,b),LessThan(b,c)]))
sum_split_after

sum_split_before = Forall(f, Forall([a,b,c],
                            Equals(Sum(x,fx,Interval(a,c)),
                                   Add(Sum(x,fx,Interval(a,Sub(b, one))),
                                       Sum(x,fx,Interval(b,c)))),
                                  domain=Integer, conditions=[LessThan(a,b),LessThanEquals(b,c)]))
sum_split_before

sum_split_first = Forall(f, Forall([a,b],
                                 Equals(Sum(x,fx,Interval(a,b)),
                                        Add(fa, Sum(x,fx,Interval(Add(a, one),b)))),
                                 domain=Integer, conditions=[LessThan(a,b)]))
sum_split_first

sum_zero_and_one = Forall(f, Equals(Sum(n, Operation(f, n), Interval(zero, one)),
                                Add(Operation(f, zero), Operation(f, one))))
sum_zero_and_one

index_shift = Forall(f,
       Forall([a,b,c],Equals(Sum(x,Operation(f,x),Interval(a,b)),
              Sum(x,Operation(f,Sub(x,c)),Interval(Add(a,c),Add(b,c)))),domain=Integer))
index_shift

inf_geom_sum = Forall(x,Equals(Sum(m,Exp(x,m),Interval(zero,infinity)), 
             frac(one,Sub(one,x))),
              domain=Complex
              )
inf_geom_sum

fin_geom_sum = Forall([x,k,l],
                Equals(Sum(m,Exp(x,m),Interval(k,l)), 
                 frac(Sub(Exp(x,Add(l,one)),Exp(x,k)),Sub(x,one))),
                 conditions=[InSet(k,Integer),
                  InSet(l,Integer),
                  InSet(x,Complex),
                  LessThan(k,l)])
fin_geom_sum

same_sums = Forall([f,g],
                  Forall([m,n],
                         Implies(Forall(k, 
                                        Equals(Operation(f,k),Operation(g,k)),
                                        domain=Interval(m,n)), 
                                 Equals(Sum(l,Operation(f,l),Interval(m,n)), Sum(l,Operation(g,l),Interval(m,n)))
                                 ),
                        domain=Integer))
same_sums

# Could also make such a theorem to apply whenever addition is commutative, not just for the Complex numbers.
equiv_sums = Forall((f, g, R, S),
                   Implies(Forall(a, InSet(fa, Complex), domain=R),
                           Equals(Sum(x, fx, domain=R),
                                  Sum(y, Operation(f, gy), domain=S))),
                  conditions=[Equals(SetOfAll(y, gy, domain=S), R)])
equiv_sums

bounded_sum = Forall((S, f, g), Implies(Forall(x, LessThanEquals(fx, gx), domain=S), 
                                     LessThanEquals(Sum(x, fx, domain=S),
                                               Sum(x, gx, domain=S))))
bounded_sum


end_theorems(locals(), __package__)
