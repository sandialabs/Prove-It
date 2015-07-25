from proveit.statement import Theorems
from proveit.basiclogic.set.setOps import In
from proveit.basiclogic.boolean.boolOps import And
from proveit.number.variables import *
from proveit.basiclogic import Forall, Exists, Equals
from proveit.number.arithmeticOps import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals, Fraction
from proveit.number.arithmeticOps import Add, Subtract, Multiply, Abs, Exponentiate, Neg

setTheorems = Theorems(__package__, locals())

inComplexes = Forall(a,
                    In(a,Complexes),
                    domain = Reals)

divIneqThm1 = Forall([a,b,c],
                    LessThanEquals(Fraction(a,b),Fraction(c,b)),
                    domain=Reals,
                    conditions=(LessThanEquals(a,c),GreaterThan(b,zero))
                    )
                    
divIneqThm2 = Forall([a,b,c],
                    LessThanEquals(Fraction(a,b),Fraction(a,c)),
                    domain=Reals,
                    conditions=(
                                GreaterThanEquals(b,c),
                                GreaterThanEquals(a,zero),
                                GreaterThan(b,zero),
                                GreaterThan(c,zero)
                                )
                    )

ineqThm3 = Forall([theta],
                   GreaterThanEquals(
                            Abs(
                                Subtract(
                                        one, Exponentiate(
                                                          e,
                                                          Multiply(i,theta)
                                                          )
                                        )
                                ),
                                Fraction(
                                        Multiply(
                                                two, Abs(theta)
                                                ),
                                        pi
                                        )
                                ),
                    domain = Reals,
                    conditions = (LessThanEquals(Neg(pi),theta),
                                  LessThanEquals(theta,pi))
                    )

ineqThm4 = Forall([l,t,delta], And(
                                LessThanEquals(
                                                Neg(pi),
                                                Multiply(
                                                    Multiply(two,pi),
                                                    Subtract(delta,
                                                    Fraction(
                                                             l,
                                                             Exponentiate(
                                                                          two,
                                                                          t
                                                                          )
                                                            )
                                                            )
                                                         )
                                              ),
                                LessThanEquals(
                                                Multiply(
                                                    Multiply(two,pi),
                                                    Subtract(delta,
                                                    Fraction(
                                                             l,
                                                             Exponentiate(
                                                                          two,
                                                                          t
                                                                          )
                                                            )
                                                            )
                                                         ),
                                                pi
                                              )
                            ),
                    conditions = (
                                  In(l,Integers),
                                  In(t,Naturals),
                                  In(delta,Reals),
                                  LessThanEquals(
                                           Neg(Exponentiate(two,Subtract(t,one))),
                                           l),
                                  LessThanEquals(
                                            l,
                                            Exponentiate(two,Subtract(t,one))
                                                ),
                                  LessThanEquals(zero,delta),
                                  LessThanEquals(delta,Exponentiate(two,Neg(t)))
                                  )
                )

squarePosIneq = Forall([a,b],
                        LessThanEquals(Exponentiate(Abs(a),two),Exponentiate(b,two)),
                        domain = Reals,
                        conditions = (LessThanEquals(Abs(a),b),))

squarePosEq = Forall(a,
                     Equals(Exponentiate(Abs(a),two),Exponentiate(a,two)),
                     domain = Reals)

ineqThm5 = Forall([a,b,c],
                  GreaterThanEquals(Multiply(c,a),Multiply(c,b)),
                  domain = Reals,
                  conditions = (GreaterThan(c,zero),GreaterThanEquals(a,b)))
         
ineqThm6 = Forall([a,b],
                  GreaterThanEquals(Add(a,b),a),
                  domain = Reals,
                  conditions = GreaterThanEquals(b,zero))
                  
ineqThm7 = Forall([x,l],
                  LessThanEquals(
                                Fraction(one,Exponentiate(Subtract(l,x),two)),
                                Fraction(one,Exponentiate(l,two))
                                ),
                  domain = Reals,
                  conditions = (LessThanEquals(l,zero),
                                LessThanEquals(zero,x),
                                LessThanEquals(x,one)))

ineqThm8 = Forall([x,l],
                  LessThanEquals(
                                Fraction(one,Exponentiate(Subtract(l,x),two)),
                                Fraction(one,Exponentiate(Subtract(l,one),two)),
                                ),
                  domain = Reals,
                  conditions = (GreaterThan(l,zero),
                                LessThanEquals(zero,x),
                                LessThanEquals(x,one)))



setTheorems.finish(locals())
