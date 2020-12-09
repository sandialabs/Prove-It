from proveit.logic import Forall, Or, Equals, Implies
from proveit.numbers import Real
from proveit.numbers import Less, LessEq, Greater, GreaterEq
from proveit.common import x, y, z
from proveit import beginAxioms, endAxioms

beginAxioms(locals())

lessThanEqualsDef = Forall([x, y], Or(Less(x, y), Equals(x, y)), domain=Real, conditions=LessEq(x, y))
lessThanEqualsDef

greaterThanEqualsDef = Forall([x, y], Or(Greater(x, y), Equals(x, y)), domain=Real, conditions=GreaterEq(x, y))
greaterThanEqualsDef

reverseGreaterThanEquals = Forall((x, y), Implies(GreaterEq(x, y), LessEq(y, x)))
reverseGreaterThanEquals

reverseLessThanEquals = Forall((x, y), Implies(LessEq(x, y), GreaterEq(y, x)))
reverseLessThanEquals

reverseGreaterThan = Forall((x, y), Implies(Greater(x, y), Less(y, x)))
reverseGreaterThan

reverseLessThan = Forall((x, y), Implies(Less(x, y), Greater(y, x)))
reverseLessThan

greaterThanEqualsDef = Forall((x,y), Implies(GreaterEq(x,y), Or(Greater(x,y),Equals(x,y))))
greaterThanEqualsDef

lessThanEqualsDef = Forall((x,y), Implies(LessEq(x,y), Or(Less(x,y),Equals(x,y))))
lessThanEqualsDef

lessThanTransLessThanRight = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(Less(y,z),
                                             Less(x,z))))
lessThanTransLessThanRight

lessThanTransLessThanEqualsRight = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(LessEq(y,z),
                                             Less(x,z))))
lessThanTransLessThanEqualsRight

lessThanTransLessThanLeft = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(Less(z,x),
                                             Less(z,y))))
lessThanTransLessThanLeft

lessThanTransLessThanEqualsLeft = Forall((x,y,z),
                               Implies(Less(x,y),
                                      Implies(LessEq(z,x),
                                             Less(z,y))))
lessThanTransLessThanEqualsLeft

lessThanEqualsTransLessThanRight = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(Less(y,z),
                                             Less(x,z))))
lessThanEqualsTransLessThanRight

lessThanEqualsTransLessThanEqualsRight = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(LessEq(y,z),
                                             LessEq(x,z))))
lessThanEqualsTransLessThanEqualsRight

lessThanEqualsTransLessThanLeft = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(Less(z,x),
                                             Less(z,y))))
lessThanEqualsTransLessThanLeft

lessThanEqualsTransLessThanEqualsLeft = Forall((x,y,z),
                               Implies(LessEq(x,y),
                                      Implies(LessEq(z,x),
                                             LessEq(z,y))))
lessThanEqualsTransLessThanEqualsLeft

greaterThanTransGreaterThanRight = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(Greater(y,z),
                                                  Greater(x,z))))
greaterThanTransGreaterThanRight

greaterThanTransGreaterThanEqualsRight = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(GreaterEq(y,z),
                                                  Greater(x,z))))
greaterThanTransGreaterThanEqualsRight

greaterThanTransGreaterThanLeft = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(Greater(z,x),
                                                  Greater(z,y))))
greaterThanTransGreaterThanLeft

greaterThanTransGreaterThanEqualsLeft = Forall((x,y,z),
                                    Implies(Greater(x,y),
                                           Implies(GreaterEq(z,x),
                                                  Greater(z,y))))
greaterThanTransGreaterThanEqualsLeft


greaterThanEqualsTransGreaterThanRight = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(Greater(y,z),
                                                             Greater(x,z))))
greaterThanEqualsTransGreaterThanRight


greaterThanEqualsTransGreaterThanEqualsRight = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(GreaterEq(y,z),
                                                             GreaterEq(x,z))))
greaterThanEqualsTransGreaterThanEqualsRight


greaterThanEqualsTransGreaterThanLeft = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(Greater(z,x),
                                                             Greater(z,y))))
greaterThanEqualsTransGreaterThanLeft

greaterThanEqualsTransGreaterThanEqualsLeft = Forall((x,y,z),
                                               Implies(GreaterEq(x,y),
                                                      Implies(GreaterEq(z,x),
                                                             GreaterEq(z,y))))
greaterThanEqualsTransGreaterThanEqualsLeft


endAxioms(locals(), __package__)
