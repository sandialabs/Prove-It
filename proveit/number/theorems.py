#from proveit.statement import Theorems
#from proveit.expression import Literal, Operation, STRING, LATEX
#from proveit.multiExpression import Etcetera
#from proveit.basiclogic import BOOLEANS, Forall, Exists, And, Or, Implies, Iff, Equals
#from setOps import In, NotIn, Singleton, Union, Intersection, SubsetEq, SupersetEq, SetOfAll
#from proveit.basiclogic.variables import f, x, y, A, B, C, S, P
#from proveit.basiclogic.simpleExpr import fy, Px, Py

#from proveit.number.arithmeticOps import *
from proveit.statement import Theorems
from proveit.number.arithmeticOps import Summation, Exponentiate, DiscreteContiguousSet, Fraction, Subtract, Add, LessThan
from proveit.number.arithmeticOps import LessThanEquals
#from proveit.expression import Literal
#from proveit.basiclogic.boolean.quantifiers import Forall, Exists
from proveit.basiclogic import Forall, Exists, Equals

from proveit.number.variables import A, a,b,c,m,n,r, t,eps,phi,U,SUm,C2m,H,Hm,u,e,i,pi,k,l,r,zero,one,two,infinity
from proveit.number.variables import minusOne, minusTwo,Z,Zp,R,zeroToOne,tFunc,tFunc_n_eps,QPE,QPEfunc, Am

#from proveit.basiclogic.boolean.quantifiers import Forall, Exists, Equals
from proveit.basiclogic.set.setOps import In
#from proveit.basiclogic.equality.eqOps import Equals

setTheorems = Theorems(__package__, locals())

#Formula for infinite geometric sum
infGeomSum = Forall(r,Equals(Summation(m,Exponentiate(r,m),DiscreteContiguousSet(zero,infinity)), 
             Fraction(one,Subtract(one,r))),
              domain=R
              )

#Formula for finitie geometric sum              
finGeomSum = Forall([r,k,l],
                Equals(Summation(m,Exponentiate(r,m),DiscreteContiguousSet(k,l)), 
                 Fraction(Subtract(Exponentiate(r,Add(l,one)),Exponentiate(r,k)),Subtract(r,one))),
                 conditions=[In(k,Z),
                  In(l,Z),
                  In(r,R),
                  LessThan(k,l)])

#addComm = 
#Sum of f(x) from a to c equals sum of f(x) from a to b plus sum of f(x) from b+1 to c
splitSum = Forall([a,b,c,A],
                  Equals(Summation(m,Am,DiscreteContiguousSet(a,c)),
                         Add(Summation(m,Am,DiscreteContiguousSet(a,b)),
                             Summation(m,Am,DiscreteContiguousSet(Add(b,one),c)))),
                  conditions=[In(a,Z),In(b,Z),In(c,Z),LessThanEquals(a,b),LessThanEquals(b,c)])

setTheorems.finish(locals())

