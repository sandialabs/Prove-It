from proveit.basiclogic.boolean.axioms import existsDef
from proveit.basiclogic import Exists, Forall, Not, NotEquals, Implies, In, TRUE, deriveStmtEqTrue
from proveit.common import P, S, X, xEtc, PxEtc, etc_QxEtc, Qetc

inDomain = In(xEtc, S) # ..x.. in S
# existsNot = [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))]
existsNot = Exists(xEtc, Not(PxEtc), S, etc_QxEtc)
# [Not(forall_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) != TRUE] assuming existsNot
existsDef.specialize({PxEtc:Not(PxEtc)}).deriveRightViaEquivalence().proven({existsNot})
# forall_{..x.. in S | ..Q(..x..)..} P(..x..)
forallPx = Forall(xEtc, PxEtc, S, etc_QxEtc)
# forall_{..x.. in S | ..Q(..x..)..} Not(P(..x..)) != TRUE
forallNotPxNotTrue = Forall(xEtc, NotEquals(Not(PxEtc), TRUE), S, etc_QxEtc)
# forallPx in BOOLEANS, forallNotPxNotTrue in BOOLEANS
for expr in (forallPx, forallNotPxNotTrue):
    expr.deduceInBool().proven()
# Not(TRUE) != TRUE
NotEquals(Not(TRUE), TRUE).proveByEval()
# forallNotPxNotTrue assuming forallPx, ..Q(..x..).., In(..x.., S)
deriveStmtEqTrue(forallPx.specialize()).lhsStatementSubstitution(NotEquals(Not(X), TRUE), X).deriveConclusion().generalize(xEtc, domain=S, conditions=etc_QxEtc).proven({forallPx, inDomain})
# Not(forallNotPxNotTrue) => Not(forallPx)
Implies(forallPx, forallNotPxNotTrue).transpose().proven()
# forall_{P, ..Q.., S} [exists_{..x.. in S | ..Q(..x..)..} Not(P(..x..))] => [Not(forall_{..x.. in S | ..Q(..x..)..} P(..x..)]
Implies(existsNot, Not(forallPx)).generalize((P, Qetc, S)).qed(__file__)
