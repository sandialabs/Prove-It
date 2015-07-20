from proveit.basiclogic.boolean.axioms import existsDef
from proveit.basiclogic import Exists, Forall, Not, NotEquals, Implies, In, TRUE, deriveStmtEqTrue
from proveit.basiclogic.variables import P, S, X
from proveit.basiclogic.simpleExpr import xEtc, PxEtc, etc_QxEtc

inDomain = In(xEtc, S) # ..x.. in S
# existsNot = [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))]
existsNot = Exists(xEtc, Not(PxEtc), etc_QxEtc, domain=S)
# [Not(forall_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) != TRUE] assuming existsNot
existsDef.specialize({PxEtc:Not(PxEtc)}).deriveRightViaEquivalence().prove({existsNot})
# forall_{..x.. in S | ..Q(..x..)..} P(..x..)
forallPx = Forall(xEtc, PxEtc, etc_QxEtc, domain=S)
# forall_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) != TRUE
forallNotPxNotTrue = Forall(xEtc, NotEquals(Not(PxEtc), TRUE), etc_QxEtc, domain=S)
# forallPx in BOOLEANS, forallNotPxNotTrue in BOOLEANS
for expr in (forallPx, forallNotPxNotTrue):
    expr.deduceInBool().prove()
# Not(TRUE) != TRUE
NotEquals(Not(TRUE), TRUE).proveByEval()
# forallNotPxNotTrue assuming forallPx, ..Q(..x..).., In(..x.., S)
deriveStmtEqTrue(forallPx.specialize()).lhsStatementSubstitution(X, NotEquals(Not(X), TRUE)).deriveConclusion().generalize(xEtc, etc_QxEtc).prove({forallPx, inDomain})
# Not(forallNotPxNotTrue) => Not(forallPx)
Implies(forallPx, forallNotPxNotTrue).transpose().prove()
# forall_{P, ..Q.., S} [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))] => [Not(forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
Implies(existsNot, Not(forallPx)).generalize((P, etc_QxEtc, S)).qed(__file__)
