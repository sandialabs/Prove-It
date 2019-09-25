from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals
from proveit.number import Integers, Naturals, NaturalsPos, Reals, RealsPos, Complexes
from proveit.number import Exp, Sqrt, Add, Mult, Sub, Neg, frac, Abs, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals
from proveit.common import a, b, c, d, n, x, y, z, xEtc, xMulti
from proveit.number.common import zero, one, two
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

expNatClosure = Forall((a, b), InSet(Exp(a, b), NaturalsPos), domain=Naturals, conditions=[NotEquals(a, zero)])
expNatClosure

expRealClosure = Forall([a, b], InSet(Exp(a, b), Reals), domain=Reals,
                       conditions=[GreaterThanEquals(a, zero), GreaterThan(b, zero)])
expRealClosure

expRealPosClosure = Forall([a, b], InSet(Exp(a, b), RealsPos), domain=Reals,
                       conditions=[GreaterThan(a, zero)])
expRealPosClosure

expComplexClosure = Forall([a, b], InSet(Exp(a, b), Complexes), domain=Complexes, 
                    conditions=[NotEquals(a, zero)])
expComplexClosure

sqrtRealClosure = Forall([a], InSet(Sqrt(a), Reals), domain=Reals,
                         conditions=[GreaterThanEquals(a, zero)])
sqrtRealClosure

sqrtRealPosClosure = Forall([a], InSet(Sqrt(a), RealsPos), domain=RealsPos)
sqrtRealPosClosure

sqrtComplexClosure = Forall([a], InSet(Sqrt(a), Complexes), domain=Complexes)
sqrtComplexClosure

# Should generalize to even power closure, but need to define and implement evens set to do this.
sqrdPosClosure = Forall(a, InSet(Exp(a, two), RealsPos), 
                        domain=Reals, conditions=[NotEquals(a, zero)])
sqrdPosClosure

squarePosIneq = Forall([a,b],
                        LessThanEquals(Exp(Abs(a),two),Exp(b,two)),
                        domain = Reals,
                        conditions = (LessThanEquals(Abs(a),b),))
squarePosIneq

squarePosEq = Forall(a,
                     Equals(Exp(Abs(a),two),Exp(a,two)),
                     domain = Reals)
squarePosEq

expNotEqZero = Forall([a, b], NotEquals(Exp(a,b), zero), domain=Complexes, conditions=[NotEquals(a, zero)])
expNotEqZero

expZeroEqOne = Forall([a], Equals(Exp(a, zero), one), domain=Complexes, conditions=[NotEquals(a, zero)])
expZeroEqOne

exponentiatedZero = Forall([x], Equals(Exp(zero, x), zero), domain=Complexes, conditions=[NotEquals(x, zero)])
exponentiatedZero

exponentiatedOne = Forall([x], Equals(Exp(one, x), one), domain=Complexes)
exponentiatedOne

sumInExp = Forall([a,b,c],
                Equals(Exp(a,Add(b,c)),
                       Mult(Exp(a,b),Exp(a,c))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
sumInExp

sumInExpRev = Forall([a,b,c],
                Equals(Mult(Exp(a,b),Exp(a,c)),
                       Exp(a,Add(b,c))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
sumInExpRev

addOneRightInExp = Forall([a,b],
                Equals(Exp(a,Add(b,one)),
                       Mult(Exp(a,b),a)),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneRightInExp

addOneRightInExpRev = Forall([a,b],
                Equals(Mult(Exp(a,b),a),
                       Exp(a,Add(b,one))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneRightInExpRev


addOneLeftInExp = Forall([a,b],
                Equals(Exp(a,Add(one, b)),
                       Mult(a, Exp(a,b))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneLeftInExp

addOneLeftInExpRev = Forall([a,b],
                Equals(Mult(a, Exp(a,b)),
                       Exp(a,Add(one, b))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
addOneLeftInExpRev


diffInExp = Forall([a,b,c],
                Equals(Exp(a,Sub(b,c)),
                       Mult(Exp(a,b),Exp(a,Neg(c)))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
diffInExp


diffInExpRev = Forall([a,b,c],
                Equals(Mult(Exp(a,b),Exp(a,Neg(c))),
                       Exp(a,Sub(b,c))),
                domain = Complexes, conditions=[NotEquals(a, zero)])
diffInExpRev

diffFracInExp = Forall([a,b,c,d],
                Equals(Exp(a,Sub(b,frac(c, d))),
                       Mult(Exp(a,b),Exp(a,frac(Neg(c), d)))),
                domain = Complexes, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diffFracInExp


diffFracInExpRev = Forall([a,b,c,d],
                Equals(Mult(Exp(a,b),Exp(a,frac(Neg(c), d))),
                       Exp(a,Sub(b,frac(c, d)))),
                domain = Complexes, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diffFracInExpRev

# works because log[a^c b^c] = c log a + c log b
expOfPositivesProd = Forall(c, Forall((a, b),
                             Equals(Exp(Mult(a,b),c),
                                    Mult(Exp(a,c),Exp(b,c))),
                             domain=RealsPos),
                domain=Complexes)
expOfPositivesProd

expOfPositivesProdRev = Forall(c, Forall((a, b),
                             Equals(Mult(Exp(a,c),Exp(b,c)),
                                   Exp(Mult(a,b),c)),
                             domain=RealsPos),
                domain=Complexes)
expOfPositivesProdRev

# Works for integers powers by the commutivity of complex numbers (or their inverses when n < 0).
# Does not work for fractional powers.  Consider sqrt(-1)*sqrt(-1) = -1 not sqrt((-1)*(-1)) = 1.
intExpOfProd = Forall(n, Forall((a, b),
                                Equals(Exp(Mult(a,b),n),
                                       Mult(Exp(a,n),Exp(b,n))),
                                domain=Complexes, conditions=[NotEquals(a, zero), NotEquals(b, zero)]),
                      domain=Integers)
intExpOfProd


intExpOfProdRev = Forall(n, Forall((a, b),
                                   Equals(Mult(Exp(a,n),Exp(b,n)),
                                          Exp(Mult(a,b),n)),
                                   domain=Complexes, conditions=[NotEquals(a, zero), NotEquals(b, zero)]),
                         domain=Integers)
intExpOfProdRev

natsPosExpOfProd = Forall(n, Forall((a, b),
                                    Equals(Exp(Mult(a,b),n),
                                           Mult(Exp(a,n),Exp(b,n))),
                                    domain=Complexes),
                          domain=NaturalsPos)
natsPosExpOfProd

natsPosExpOfProdRev = Forall(n, Forall((a, b),
                                       Equals(Mult(Exp(a,n),Exp(b,n)),
                                              Exp(Mult(a,b),n)),
                                       domain=Complexes),
                             domain=NaturalsPos)
natsPosExpOfProdRev

# Works for integers powers through repetition of a^b (or a^{-b}) and adding exponents.
# Does not work for fractional powers.  Consider sqrt[(-1)^2] = 1 not (-1)^{2*(1/2)} = -1.
intExpOfExp = Forall(n, Forall((a, b), 
                            Equals(Exp(Exp(a, b), n), 
                                   Exp(a, Mult(b, n))), 
                            domain=Complexes, conditions=[NotEquals(a, zero)]), 
                  domain=Integers)
intExpOfExp

intExpOfNegExp = Forall(n, Forall((a, b), 
                               Equals(Exp(Exp(a, Neg(b)), n), 
                                      Exp(a, Neg(Mult(b, n)))),
                               domain=Complexes, conditions=[NotEquals(a, zero)]), 
                        domain=Integers)
intExpOfNegExp

negIntExpOfExp = Forall(n, Forall((a, b),
                            Equals(Exp(Exp(a, b), Neg(n)), 
                                   Exp(a, Neg(Mult(b, n)))), 
                               domain=Complexes, conditions=[NotEquals(a, zero)]),
                        domain=Integers)

negIntExpOfExp

negIntExpOfNegExp = Forall(n, Forall((a, b),
                                     Equals(Exp(Exp(a, Neg(b)), Neg(n)), 
                                            Exp(a, Mult(b, n))), 
                               domain=Complexes, conditions=[NotEquals(a, zero)]),
                           domain=Integers)

negIntExpOfNegExp

diffSquareComm = Forall([a,b],
                        Equals(
                            Exp(Sub(a,b),two),
                            Exp(Sub(b,a),two)),
                        domain = Complexes)
diffSquareComm

oneExp = Forall([x],
               Equals(Exp(x,one),
                      x),
               domain = Complexes)
oneExp

expOne = Forall([x],
               Equals(Exp(one,x),
                     one),
               domain = Complexes)
expOne

sameExpDistribute = Forall([x,y,z],
                            Equals(Mult(Exp(x,y),Exp(z,y)),
                                 Exp(Mult(x,z),y)),
                            domain = Complexes)
sameExpDistribute

sqrtOfProd = Forall(xEtc, Equals(Sqrt(Mult(xEtc)),
                              Mult(Etcetera(Sqrt(xMulti)))),
                  domain=RealsPos)
sqrtOfProd

prodOfSqrts = Forall(xEtc, Equals(Mult(Etcetera(Sqrt(xMulti))),
                                  Sqrt(Mult(xEtc))),
                     domain=RealsPos)
prodOfSqrts

sqrtTimesItself = Forall(x, Equals(Mult(Sqrt(x), Sqrt(x)), x),
                         domain=Reals, conditions=[GreaterThanEquals(x, zero)])
sqrtTimesItself

endTheorems(locals(), __package__)
