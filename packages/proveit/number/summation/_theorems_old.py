from proveit import Operation
from proveit.logic import Forall, Implies, InSet, Equals, SetOfAll
from proveit.number import Integers, Reals, Complexes
from proveit.number import Sum, Interval, Exp, frac, Sub, Add, LessThan, LessThanEquals
from proveit.common import a, b, c, f, g, k, l, m, n, x, y, fa, fx, gx, gy, xMulti, xEtc, P, R, S, PxEtc
from proveit.number.common import zero, one, infinity

from proveit import beginTheorems, endTheorems

beginTheorems(locals())

summationRealClosure = Forall([P, S], Implies(Forall(xMulti, InSet(PxEtc, Reals), domain=S), 
                                              InSet(Sum(xMulti, PxEtc, domain=S), Reals)))
summationRealClosure

summationComplexClosure = Forall([P, S], Implies(Forall(xMulti, InSet(PxEtc, Complexes), domain=S), 
                                          InSet(Sum(xMulti, PxEtc, domain=S), Complexes)))
summationComplexClosure


sumSplitAfter = Forall(f, Forall([a,b,c],
                            Equals(Sum(x,fx,Interval(a,c)),
                                   Add(Sum(x,fx,Interval(a,b)),
                                       Sum(x,fx,Interval(Add(b,one),c)))),
                                 domain=Integers, conditions=[LessThanEquals(a,b),LessThan(b,c)]))
sumSplitAfter

sumSplitBefore = Forall(f, Forall([a,b,c],
                            Equals(Sum(x,fx,Interval(a,c)),
                                   Add(Sum(x,fx,Interval(a,Sub(b, one))),
                                       Sum(x,fx,Interval(b,c)))),
                                  domain=Integers, conditions=[LessThan(a,b),LessThanEquals(b,c)]))
sumSplitBefore

sumSplitFirst = Forall(f, Forall([a,b],
                                 Equals(Sum(x,fx,Interval(a,b)),
                                        Add(fa, Sum(x,fx,Interval(Add(a, one),b)))),
                                 domain=Integers, conditions=[LessThan(a,b)]))
sumSplitFirst

sumZeroAndOne = Forall(f, Equals(Sum(n, Operation(f, n), Interval(zero, one)),
                                Add(Operation(f, zero), Operation(f, one))))
sumZeroAndOne

indexShift = Forall(f,
       Forall([a,b,c],Equals(Sum(x,Operation(f,x),Interval(a,b)),
              Sum(x,Operation(f,Sub(x,c)),Interval(Add(a,c),Add(b,c)))),domain=Integers))
indexShift

infGeomSum = Forall(x,Equals(Sum(m,Exp(x,m),Interval(zero,infinity)), 
             frac(one,Sub(one,x))),
              domain=Complexes
              )
infGeomSum

finGeomSum = Forall([x,k,l],
                Equals(Sum(m,Exp(x,m),Interval(k,l)), 
                 frac(Sub(Exp(x,Add(l,one)),Exp(x,k)),Sub(x,one))),
                 conditions=[InSet(k,Integers),
                  InSet(l,Integers),
                  InSet(x,Complexes),
                  LessThan(k,l)])
finGeomSum

sameSums = Forall([f,g],
                  Forall([m,n],
                         Implies(Forall(k, 
                                        Equals(Operation(f,k),Operation(g,k)),
                                        domain=Interval(m,n)), 
                                 Equals(Sum(l,Operation(f,l),Interval(m,n)), Sum(l,Operation(g,l),Interval(m,n)))
                                 ),
                        domain=Integers))
sameSums

# Could also make such a theorem to apply whenever addition is commutative, not just Complexes.
equivSums = Forall((f, g, R, S),
                   Implies(Forall(a, InSet(fa, Complexes), domain=R),
                           Equals(Sum(x, fx, domain=R),
                                  Sum(y, Operation(f, gy), domain=S))),
                  conditions=[Equals(SetOfAll(y, gy, domain=S), R)])
equivSums

boundedSum = Forall((S, f, g), Implies(Forall(x, LessThanEquals(fx, gx), domain=S), 
                                     LessThanEquals(Sum(x, fx, domain=S),
                                               Sum(x, gx, domain=S))))
boundedSum


endTheorems(locals(), __package__)
