from proveit.logic import Forall, Or, Equals, Implies
from proveit.number import Reals
from proveit.number import LessThan, LessThanEquals, GreaterThan, GreaterThanEquals
from proveit.common import x, y, z
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

lessThanEqualsDef = Forall([x, y], Or(LessThan(x, y), Equals(x, y)), domain=Reals, conditions=LessThanEquals(x, y))
lessThanEqualsDef

greaterThanEqualsDef = Forall([x, y], Or(GreaterThan(x, y), Equals(x, y)), domain=Reals, conditions=GreaterThanEquals(x, y))
greaterThanEqualsDef

reverseGreaterThanEquals = Forall((x, y), Implies(GreaterThanEquals(x, y), LessThanEquals(y, x)))
reverseGreaterThanEquals

reverseLessThanEquals = Forall((x, y), Implies(LessThanEquals(x, y), GreaterThanEquals(y, x)))
reverseLessThanEquals

reverseGreaterThan = Forall((x, y), Implies(GreaterThan(x, y), LessThan(y, x)))
reverseGreaterThan

reverseLessThan = Forall((x, y), Implies(LessThan(x, y), GreaterThan(y, x)))
reverseLessThan

greaterThanEqualsDef = Forall((x,y), Implies(GreaterThanEquals(x,y), Or(GreaterThan(x,y),Equals(x,y))))
greaterThanEqualsDef

lessThanEqualsDef = Forall((x,y), Implies(LessThanEquals(x,y), Or(LessThan(x,y),Equals(x,y))))
lessThanEqualsDef

lessThanTransLessThanRight = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThan(y,z),
                                             LessThan(x,z))))
lessThanTransLessThanRight

lessThanTransLessThanEqualsRight = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThanEquals(y,z),
                                             LessThan(x,z))))
lessThanTransLessThanEqualsRight

lessThanTransLessThanLeft = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThan(z,x),
                                             LessThan(z,y))))
lessThanTransLessThanLeft

lessThanTransLessThanEqualsLeft = Forall((x,y,z),
                               Implies(LessThan(x,y),
                                      Implies(LessThanEquals(z,x),
                                             LessThan(z,y))))
lessThanTransLessThanEqualsLeft

lessThanEqualsTransLessThanRight = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThan(y,z),
                                             LessThan(x,z))))
lessThanEqualsTransLessThanRight

lessThanEqualsTransLessThanEqualsRight = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThanEquals(y,z),
                                             LessThanEquals(x,z))))
lessThanEqualsTransLessThanEqualsRight

lessThanEqualsTransLessThanLeft = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThan(z,x),
                                             LessThan(z,y))))
lessThanEqualsTransLessThanLeft

lessThanEqualsTransLessThanEqualsLeft = Forall((x,y,z),
                               Implies(LessThanEquals(x,y),
                                      Implies(LessThanEquals(z,x),
                                             LessThanEquals(z,y))))
lessThanEqualsTransLessThanEqualsLeft

greaterThanTransGreaterThanRight = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThan(y,z),
                                                  GreaterThan(x,z))))
greaterThanTransGreaterThanRight

greaterThanTransGreaterThanEqualsRight = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThanEquals(y,z),
                                                  GreaterThan(x,z))))
greaterThanTransGreaterThanEqualsRight

greaterThanTransGreaterThanLeft = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThan(z,x),
                                                  GreaterThan(z,y))))
greaterThanTransGreaterThanLeft

greaterThanTransGreaterThanEqualsLeft = Forall((x,y,z),
                                    Implies(GreaterThan(x,y),
                                           Implies(GreaterThanEquals(z,x),
                                                  GreaterThan(z,y))))
greaterThanTransGreaterThanEqualsLeft


greaterThanEqualsTransGreaterThanRight = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThan(y,z),
                                                             GreaterThan(x,z))))
greaterThanEqualsTransGreaterThanRight


greaterThanEqualsTransGreaterThanEqualsRight = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThanEquals(y,z),
                                                             GreaterThanEquals(x,z))))
greaterThanEqualsTransGreaterThanEqualsRight


greaterThanEqualsTransGreaterThanLeft = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThan(z,x),
                                                             GreaterThan(z,y))))
greaterThanEqualsTransGreaterThanLeft

greaterThanEqualsTransGreaterThanEqualsLeft = Forall((x,y,z),
                                               Implies(GreaterThanEquals(x,y),
                                                      Implies(GreaterThanEquals(z,x),
                                                             GreaterThanEquals(z,y))))
greaterThanEqualsTransGreaterThanEqualsLeft


endAxioms(locals(), __package__)
