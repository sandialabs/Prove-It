from proveit.basiclogic.boolean.axioms import existsDef
from proveit.basiclogic import Equals, Or
from proveit.basiclogic.variables import P, S, X
from proveit.basiclogic.simpleExpr import etcQ

# exists_{..x.. in S | ..Q(..x..)..} P(..x..) = not(forall_{..x.. | ..Q(..x..)..} P(..x..) != TRUE)
existsDefSpec = existsDef.specialize().prove()
# [not(forall_{..x.. in S | ..Q(..x..)..} P(..x..) != TRUE) = TRUE] or [not(forall_{..x.. in S| ..Q(..x..)..} P(..x..) != TRUE) = FALSE]
rhsTrue, rhsFalse = existsDefSpec.rhs.deduceInBool().unfold().prove().operands
# exists_{..x.. in S | ..Q(..x..)..} P(..x..) in BOOLEANS assuming [not(forall_{..x.. in S | ..Q(..x..)..} P(..x..) != TRUE) = TRUE]
existsInBoolSpec = rhsTrue.rhsSubstitute(X, Equals(existsDefSpec.lhs, X)).inBoolViaBooleanEquality().prove({rhsTrue})
# exists_{..x.. | ..Q(..x..)..} P(..x..) in BOOLEANS assuming [not(forall_{..x.. in S | ..Q..(..x..)} P(..x..) != TRUE) = FALSE]
rhsFalse.rhsSubstitute(X, Equals(existsDefSpec.lhs, X)).inBoolViaBooleanEquality().prove({rhsFalse})
# deduce rhsTrue, rhsFals, existsInBoolSpec all in BOOLEANS
for expr in (rhsTrue, rhsFalse, existsInBoolSpec): expr.deduceInBool()
# forall_{P, ..Q.., S} exists_{..x.. | ..Q(..x..)..} P(..x..) in BOOLEANS
Or(rhsTrue, rhsFalse).deriveCommonConclusion(existsInBoolSpec).generalize((P, etcQ, S)).qed(__file__)
