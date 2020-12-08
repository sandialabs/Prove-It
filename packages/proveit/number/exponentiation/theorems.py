from proveit import Etcetera
from proveit.logic import Forall, InSet, Equals, NotEquals
from proveit.number import Integer, Natural, NaturalPos, Real, RealPos, Complex
from proveit.number import Exp, sqrt, Add, Mult, Sub, Neg, frac, Abs, GreaterThan, GreaterThanEquals, LessThan, LessThanEquals
from proveit.common import a, b, c, d, n, x, y, z, xEtc, xMulti
from proveit.number.common import zero, one, two
from proveit import beginTheorems, endTheorems

beginTheorems(locals())

expNatClosure = Forall((a, b), InSet(Exp(a, b), NaturalPos), domain=Natural, conditions=[NotEquals(a, zero)])
expNatClosure

expRealClosure = Forall([a, b], InSet(Exp(a, b), Real), domain=Real,
                       conditions=[GreaterThanEquals(a, zero), GreaterThan(b, zero)])
expRealClosure

expRealPosClosure = Forall([a, b], InSet(Exp(a, b), RealPos), domain=Real,
                       conditions=[GreaterThan(a, zero)])
expRealPosClosure

expComplexClosure = Forall([a, b], InSet(Exp(a, b), Complex), domain=Complex, 
                    conditions=[NotEquals(a, zero)])
expComplexClosure

sqrtRealClosure = Forall([a], InSet(sqrt(a), Real), domain=Real,
                         conditions=[GreaterThanEquals(a, zero)])
sqrtRealClosure

sqrtRealPosClosure = Forall([a], InSet(sqrt(a), RealPos), domain=RealPos)
sqrtRealPosClosure

sqrtComplexClosure = Forall([a], InSet(sqrt(a), Complex), domain=Complex)
sqrtComplexClosure

# Should generalize to even power closure, but need to define and implement evens set to do this.
sqrdPosClosure = Forall(a, InSet(Exp(a, two), RealPos), 
                        domain=Real, conditions=[NotEquals(a, zero)])
sqrdPosClosure

squarePosIneq = Forall([a,b],
                        LessThanEquals(Exp(Abs(a),two),Exp(b,two)),
                        domain = Real,
                        conditions = (LessThanEquals(Abs(a),b),))
squarePosIneq

squarePosEq = Forall(a,
                     Equals(Exp(Abs(a),two),Exp(a,two)),
                     domain = Real)
squarePosEq

expNotEqZero = Forall([a, b], NotEquals(Exp(a,b), zero), domain=Complex, conditions=[NotEquals(a, zero)])
expNotEqZero

expZeroEqOne = Forall([a], Equals(Exp(a, zero), one), domain=Complex, conditions=[NotEquals(a, zero)])
expZeroEqOne

exponentiatedZero = Forall([x], Equals(Exp(zero, x), zero), domain=Complex, conditions=[NotEquals(x, zero)])
exponentiatedZero

exponentiatedOne = Forall([x], Equals(Exp(one, x), one), domain=Complex)
exponentiatedOne

sumInExp = Forall([a,b,c],
                Equals(Exp(a,Add(b,c)),
                       Mult(Exp(a,b),Exp(a,c))),
                domain = Complex, conditions=[NotEquals(a, zero)])
sumInExp

sumInExpRev = Forall([a,b,c],
                Equals(Mult(Exp(a,b),Exp(a,c)),
                       Exp(a,Add(b,c))),
                domain = Complex, conditions=[NotEquals(a, zero)])
sumInExpRev

addOneRightInExp = Forall([a,b],
                Equals(Exp(a,Add(b,one)),
                       Mult(Exp(a,b),a)),
                domain = Complex, conditions=[NotEquals(a, zero)])
addOneRightInExp

addOneRightInExpRev = Forall([a,b],
                Equals(Mult(Exp(a,b),a),
                       Exp(a,Add(b,one))),
                domain = Complex, conditions=[NotEquals(a, zero)])
addOneRightInExpRev


addOneLeftInExp = Forall([a,b],
                Equals(Exp(a,Add(one, b)),
                       Mult(a, Exp(a,b))),
                domain = Complex, conditions=[NotEquals(a, zero)])
addOneLeftInExp

addOneLeftInExpRev = Forall([a,b],
                Equals(Mult(a, Exp(a,b)),
                       Exp(a,Add(one, b))),
                domain = Complex, conditions=[NotEquals(a, zero)])
addOneLeftInExpRev


diffInExp = Forall([a,b,c],
                Equals(Exp(a,Sub(b,c)),
                       Mult(Exp(a,b),Exp(a,Neg(c)))),
                domain = Complex, conditions=[NotEquals(a, zero)])
diffInExp


diffInExpRev = Forall([a,b,c],
                Equals(Mult(Exp(a,b),Exp(a,Neg(c))),
                       Exp(a,Sub(b,c))),
                domain = Complex, conditions=[NotEquals(a, zero)])
diffInExpRev

diffFracInExp = Forall([a,b,c,d],
                Equals(Exp(a,Sub(b,frac(c, d))),
                       Mult(Exp(a,b),Exp(a,frac(Neg(c), d)))),
                domain = Complex, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diffFracInExp


diffFracInExpRev = Forall([a,b,c,d],
                Equals(Mult(Exp(a,b),Exp(a,frac(Neg(c), d))),
                       Exp(a,Sub(b,frac(c, d)))),
                domain = Complex, conditions=[NotEquals(a, zero), NotEquals(d, zero)])
diffFracInExpRev

# works because log[a^c b^c] = c log a + c log b
expOfPositivesProd = Forall(c, Forall((a, b),
                             Equals(Exp(Mult(a,b),c),
                                    Mult(Exp(a,c),Exp(b,c))),
                             domain=RealPos),
                domain=Complex)
expOfPositivesProd

expOfPositivesProdRev = Forall(c, Forall((a, b),
                             Equals(Mult(Exp(a,c),Exp(b,c)),
                                   Exp(Mult(a,b),c)),
                             domain=RealPos),
                domain=Complex)
expOfPositivesProdRev

# Works for integers powers by the commutivity of complex numbers (or their inverses when n < 0).
# Does not work for fractional powers.  Consider sqrt(-1)*sqrt(-1) = -1 not sqrt((-1)*(-1)) = 1.
intExpOfProd = Forall(n, Forall((a, b),
                                Equals(Exp(Mult(a,b),n),
                                       Mult(Exp(a,n),Exp(b,n))),
                                domain=Complex, conditions=[NotEquals(a, zero), NotEquals(b, zero)]),
                      domain=Integer)
intExpOfProd


intExpOfProdRev = Forall(n, Forall((a, b),
                                   Equals(Mult(Exp(a,n),Exp(b,n)),
                                          Exp(Mult(a,b),n)),
                                   domain=Complex, conditions=[NotEquals(a, zero), NotEquals(b, zero)]),
                         domain=Integer)
intExpOfProdRev

natsPosExpOfProd = Forall(n, Forall((a, b),
                                    Equals(Exp(Mult(a,b),n),
                                           Mult(Exp(a,n),Exp(b,n))),
                                    domain=Complex),
                          domain=NaturalPos)
natsPosExpOfProd

natsPosExpOfProdRev = Forall(n, Forall((a, b),
                                       Equals(Mult(Exp(a,n),Exp(b,n)),
                                              Exp(Mult(a,b),n)),
                                       domain=Complex),
                             domain=NaturalPos)
natsPosExpOfProdRev

# Works for integers powers through repetition of a^b (or a^{-b}) and adding exponents.
# Does not work for fractional powers.  Consider sqrt[(-1)^2] = 1 not (-1)^{2*(1/2)} = -1.
intExpOfExp = Forall(n, Forall((a, b), 
                            Equals(Exp(Exp(a, b), n), 
                                   Exp(a, Mult(b, n))), 
                            domain=Complex, conditions=[NotEquals(a, zero)]), 
                  domain=Integer)
intExpOfExp

intExpOfNegExp = Forall(n, Forall((a, b), 
                               Equals(Exp(Exp(a, Neg(b)), n), 
                                      Exp(a, Neg(Mult(b, n)))),
                               domain=Complex, conditions=[NotEquals(a, zero)]), 
                        domain=Integer)
intExpOfNegExp

negIntExpOfExp = Forall(n, Forall((a, b),
                            Equals(Exp(Exp(a, b), Neg(n)), 
                                   Exp(a, Neg(Mult(b, n)))), 
                               domain=Complex, conditions=[NotEquals(a, zero)]),
                        domain=Integer)

negIntExpOfExp

negIntExpOfNegExp = Forall(n, Forall((a, b),
                                     Equals(Exp(Exp(a, Neg(b)), Neg(n)), 
                                            Exp(a, Mult(b, n))), 
                               domain=Complex, conditions=[NotEquals(a, zero)]),
                           domain=Integer)

negIntExpOfNegExp

diffSquareComm = Forall([a,b],
                        Equals(
                            Exp(Sub(a,b),two),
                            Exp(Sub(b,a),two)),
                        domain = Complex)
diffSquareComm

oneExp = Forall([x],
               Equals(Exp(x,one),
                      x),
               domain = Complex)
oneExp

expOne = Forall([x],
               Equals(Exp(one,x),
                     one),
               domain = Complex)
expOne

sameExpDistribute = Forall([x,y,z],
                            Equals(Mult(Exp(x,y),Exp(z,y)),
                                 Exp(Mult(x,z),y)),
                            domain = Complex)
sameExpDistribute

sqrtOfProd = Forall(xEtc, Equals(sqrt(Mult(xEtc)),
                              Mult(Etcetera(sqrt(xMulti)))),
                  domain=RealPos)
sqrtOfProd

prodOfSqrts = Forall(xEtc, Equals(Mult(Etcetera(sqrt(xMulti))),
                                  sqrt(Mult(xEtc))),
                     domain=RealPos)
prodOfSqrts

sqrtTimesItself = Forall(x, Equals(Mult(sqrt(x), sqrt(x)), x),
                         domain=Real, conditions=[GreaterThanEquals(x, zero)])
sqrtTimesItself

endTheorems(locals(), __package__)
