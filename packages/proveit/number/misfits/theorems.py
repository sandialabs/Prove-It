'''
Repository for theorems that were born out of expediency but I'd like to get rid of
or generalize to something more appropriate as a named theorem.
'''

from proveit import *
from proveit.logic import *
from proveit.number import *
from proveit.common import *
from proveit.number.common import *
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

# Poorly named set of inequality theorems added for specific expediant purposes.
# Some day these should be dealt with more appropriately.

divIneqThm1 = Forall([a,b,c],
                    LessThanEquals(frac(a,b),frac(c,b)),
                    domain=Reals,
                    conditions=(LessThanEquals(a,c),GreaterThan(b,zero))
                    )
divIneqThm1

divIneqThm1strong = Forall([a,b,c],
                    LessThan(frac(a,b),frac(c,b)),
                    domain=Reals,
                    conditions=(LessThan(a,c),GreaterThan(b,zero))
                    )
divIneqThm1strong

divIneqThm1cor = Forall([a,b,c],
                    LessThanEquals(Mult(b,a),Mult(b,c)),
                    domain=Reals,
                    conditions=(LessThanEquals(a,c),GreaterThan(b,zero))
                    )
divIneqThm1cor

divIneqThm2 = Forall([a,b,c],
                    LessThanEquals(frac(a,b),frac(a,c)),
                    domain=Reals,
                    conditions=(
                                GreaterThanEquals(b,c),
                                GreaterThanEquals(a,zero),
                                GreaterThan(b,zero),
                                GreaterThan(c,zero)
                                )
                    )
divIneqThm2

sumIneq2 = Forall([a,b,c,d],
                  Implies(And(LessThanEquals(a,c), LessThanEquals(b,d)), LessThanEquals(Add(a,b),Add(c,d))),
                 domain=Reals)
sumIneq2


ineqThm5 = Forall([a,b,c],
                  GreaterThanEquals(Mult(c,a),Mult(c,b)),
                  domain = Reals,
                  conditions = (GreaterThan(c,zero),GreaterThanEquals(a,b)))
ineqThm5

powIneq = Forall([a, b, c], GreaterThanEquals(Exp(a, b), Exp(a, c)), 
                 domain=Reals, conditions= (GreaterThanEquals(a, one), GreaterThanEquals(b, c)))
powIneq

ineqThm6 = Forall([a,b],
                  GreaterThanEquals(Add(a,b),a),
                  domain = Reals,
                  conditions = GreaterThanEquals(b,zero))
ineqThm6

ineqThm6a = Forall([a,b],
                  LessThanEquals(Add(a,b),a),
                  domain = Reals,
                  conditions = LessThanEquals(b,zero))
ineqThm6a

ineqThm7 = Forall([x,l],
                  LessThanEquals(
                                frac(one,Exp(Sub(l,x),two)),
                                frac(one,Exp(l,two))
                                ),
                  domain = Reals,
                  conditions = (LessThanEquals(l,zero),
                                LessThanEquals(zero,x),
                                LessThanEquals(x,one)))
ineqThm7

ineqThm7a = Forall([x],
                   Forall([a],
                       Forall([l],
                          LessThanEquals(
                                        Mult(a,frac(one,Exp(Sub(l,x),two))),
                                        Mult(a,frac(one,Exp(l,two)))
                                        ),
                          domain=Integers,
                          conditions = LessThanEquals(l,zero)),
                        domain=Reals,
                        conditions=GreaterThanEquals(a,zero)),                
                   domain = Reals,
                   conditions = (LessThanEquals(zero,x),
                                 LessThanEquals(x,one)))
ineqThm7a

ineqThm8 = Forall([x,l],
                  LessThanEquals(
                                frac(one,Exp(Sub(l,x),two)),
                                frac(one,Exp(Sub(l,one),two)),
                                ),
                  domain = Reals,
                  conditions = (GreaterThan(l,zero),
                                LessThanEquals(zero,x),
                                LessThanEquals(x,one)))
ineqThm8

ineqThm8a = Forall([x],
                Forall([a],
                   Forall([l],
                              LessThanEquals(
                                            Mult(a,frac(one,Exp(Sub(l,x),two))),
                                            Mult(a,frac(one,Exp(Sub(l,one),two))),
                                            ),
                              domain = Integers,
                              conditions = GreaterThan(l,zero)),
                        domain=Reals,
                        conditions=GreaterThanEquals(a,zero)),
                   domain = Reals, 
                   conditions = (LessThanEquals(zero,x),
                                LessThanEquals(x,one)))
ineqThm8a

ineqThm9 = Forall(theta,LessThanEquals(Abs(Sub(one,Exp(e,Mult(i,theta)))),two),domain = Reals)
ineqThm9

ineqThm10 =  Forall([w,x,y,z],LessThanEquals(w,frac(x,z)),
                    domain = Reals,
                    conditions = (LessThanEquals(w,frac(x,y)),
                                  GreaterThanEquals(y,z),
                                  GreaterThan(w,zero),
                                  GreaterThan(x,zero),
                                  GreaterThan(y,zero),
                                  GreaterThan(z,zero)))
ineqThm10

ineqThm10a =  Forall([w,x,y,z],LessThanEquals(w,frac(x,z)),
                    domain = Reals,
                    conditions = (LessThanEquals(w,frac(x,y)),
                                  GreaterThanEquals(y,z),
                                  GreaterThanEquals(w,zero),
                                  GreaterThan(x,zero),
                                  GreaterThan(y,zero),
                                  GreaterThan(z,zero)))
ineqThm10a




sumFactor_temp = Forall([a,b,c], Equals(Add(Mult(a,b), Mult(a,c)), Mult(a, Add(b,c))), domain=Reals)
sumFactor_temp


simplifyQuarterTimesTwo = Equals(Mult(frac(one,four), two), frac(one,two))
simplifyQuarterTimesTwo


boundedInvSqrdIntegral = Forall([a, b], LessThanEquals(Int(l, frac(one,Exp(l,two)), 
                                                                 IntervalCC(a, b)),
                                                       frac(one, a)),
                                domain=RealsPos, conditions=[LessThanEquals(a, b)])
boundedInvSqrdIntegral   


inverseSqrdIsEvenFunc = InSet(Lambda(l, frac(one, Exp(l, two))), EvenFuncs)
inverseSqrdIsEvenFunc


inverseSqrdIsMonDecFunc = InSet(Lambda(l, frac(one, Exp(l, two))), MonDecFuncs)
inverseSqrdIsMonDecFunc

twoSquared = Equals(Exp(two,two),four)
twoSquared

twoSubOne = Equals(Sub(two, one), one)
twoSubOne

# special theorem for expediency
subTwoAddOne = Forall(a, Equals(Add(Sub(a, two), one),
                               Sub(a, one)),
                     domain=Complexes)
subTwoAddOne

# special theorem for expediency
outerCancel = Forall((a, b), Equals(Add(a, Sub(b, a)),
                                   b),
                    domain=Complexes)
outerCancel

addTwice = Forall([a],
                  Equals(Add(a,a), Mult(two, a)),
                 domain=Complexes)
addTwice

squarePosIneq = Forall([a],
                       Forall([b],
                            LessThanEquals(Exp(Abs(a),two),Exp(b,two)),
                            domain = Reals,
                            conditions = (LessThanEquals(Abs(a),b),)),
                       domain = Complexes)
squarePosIneq

notEq_iff_diffNotZero = Forall((a, b), Iff(NotEquals(a, b), NotEquals(Sub(a, b), zero)), domain=Complexes)
notEq_iff_diffNotZero

sumIntegrateIneq1 = Forall(f,
                    Forall([a,b],LessThanEquals(Sum(x,Operation(f,x),Interval(a,b)),
                    Add(fa, Int(x,Operation(f,x),IntervalCC(a,b)))),
                    domain=Integers,conditions=LessThanEquals(a,b)),
                    domain=MonDecFuncs)
sumIntegrateIneq1


sumIneq1 = Forall([a,b],
                  Forall([m,n],
                         Implies(Forall(k, 
                                        LessThanEquals(Operation(a,k),Operation(b,k)),
                                        domain=Interval(m,n)), 
                                 LessThanEquals(Sum(l,Operation(a,l),Interval(m,n)), Sum(l,Operation(b,l),Interval(m,n)))
                                 ),
                        domain=Integers))
sumIneq1


evenFuncSum = Forall(f,
                     Forall([a,b],
                           Equals(Sum(x,Operation(f,x),Interval(a,b)),
                                  Sum(x,Operation(f,x),Interval(Neg(b),Neg(a)))),
                            domain = Integers),
                    domain = EvenFuncs
                    )
evenFuncSum

endTheorems(locals(), __package__)
