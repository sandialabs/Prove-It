from proveit import (asExpression, Literal, Operation, safeDummyVar,
                     USE_DEFAULTS)
from proveit._common_ import A, B, C, x
from proveit._common_ import f, S
from .containment_relation import (
        ContainmentRelation, ContainmentSequence, makeSequenceOrRelation)

class SubsetRelation(ContainmentRelation):
    def __init__(self, operator, subset, superset):
        ContainmentRelation.__init__(self, operator, subset, superset)
        self.subset = self.operands[0]
        self.superset = self.operands[1]

    @staticmethod
    def WeakRelationClass():
        return SubsetEq

    @staticmethod
    def StrongRelationClass():
        return ProperSubset

    @staticmethod
    def SequenceClass():
        return SubsetSequence

class SubsetSequence(ContainmentSequence):
    def __init__(self, operators, operands):
        ContainmentSequence.__init__(self, operators, operands)

    @staticmethod
    def RelationClass():
        return SubsetRelation

def subsetSequence(operators, operands):
    '''
    Create a SubsetSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    return makeSequenceOrRelation(SubsetSequence, operators, operands)

class SubsetEq(SubsetRelation):
    # operator of the SubsetEq operation
    _operator_ = Literal(stringFormat='subseteq', latexFormat=r'\subseteq',
                         theory=__file__)

    # map left-hand-sides to SubsetEq Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()
    # map right-hand-sides to SubsetEq Judgments
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()

    def __init__(self, subset, superset):
        SubsetRelation.__init__(self, SubsetEq._operator_, subset, superset)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B, derive B supseteq A.
        '''
        from ._theorems_ import reverseSubsetEq
        return reverseSubsetEq.instantiate(
                {A:self.subset, B:self.superset}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit import ProofFailure
        from proveit.logic import SetOfAll, Equals

        # Any set contains itself
        try:
            Equals(*self.operands).prove(assumptions, automation=False)
            return self.concludeViaEquality(assumptions)
        except ProofFailure:
            pass

        try:
            # Attempt a transitivity search
            return ContainmentRelation.conclude(self, assumptions)
        except ProofFailure:
            pass # transitivity search failed

        # Check for special case of [{x | Q*(x)}_{x \in S}] \subseteq S
        if isinstance(self.subset, SetOfAll):
            from proveit.logic.set_theory.comprehension._theorems_ import (
                    comprehensionIsSubset)
            setOfAll = self.subset
            if (len(setOfAll.allInstanceVars())==1 and
                setOfAll.instanceElement == setOfAll.allInstanceVars()[0] and
                setOfAll.domain==self.superset):
                Q_op, Q_op_sub = (
                        Operation(QQ, setOfAll.allInstanceVars()),
                        setOfAll.conditions)
                return comprehensionIsSubset.instantiate(
                        {S:setOfAll.domain, Q_op:Q_op_sub},
                        relabelMap={x:setOfAll.allInstanceVars()[0]},
                        assumptions=assumptions)

        # Finally, attempt to conclude A subseteq B via
        # forall_{x in A} x in B. Issue: Variables do not match when
        # using safeDummyVar: _x_ to x.
        # We need to automate this better; right now it is only
        # practical to do concludeAsFolded manually.
        return self.concludeAsFolded(
                elemInstanceVar=safeDummyVar(self), assumptions=assumptions)

    def concludeViaEquality(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import subsetEqViaEquality
        return subsetEqViaEquality.instantiate(
                {A: self.operands[0], B: self.operands[1]},
                assumptions=assumptions)

    def unfold(self, elemInstanceVar=None, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elemInstanceVar is supplied.
        '''
        from ._theorems_ import unfoldSubsetEq
        if elemInstanceVar is not None:
            temp_result = unfoldSubsetEq.instantiate(
                {A:self.subset, B:self.superset}, assumptions=assumptions)
            return temp_result.instantiate({x:elemInstanceVar},
                    num_forall_eliminations=0, assumptions=assumptions)
        return unfoldSubsetEq.instantiate(
                {A:self.subset, B:self.superset}, assumptions=assumptions)

    def deriveSupersetMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B and element x in A, derive x in B.
        '''
        from ._theorems_ import unfoldSubsetEq
        return unfoldSubsetEq.instantiate(
                {A:self.subset, B:self.superset, x:element},
                assumptions=assumptions)

    def concludeAsFolded(self, elemInstanceVar=x, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A subseteq B, from the unfolded
        version, (forall_{x in A} x in B).
        '''
        from ._theorems_ import foldSubsetEq
        return foldSubsetEq.instantiate({A:self.subset, B:self.superset, x:elemInstanceVar}, assumptions=assumptions)

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this A subseteq B
        expression and something of the form B subseteq C, B subset C,
        or B=C to obtain A subset B or A subseteq B as appropriate.
        '''
        from proveit.logic import (
                Equals, ProperSubset, ProperSuperset, SubsetEq, SupersetEq)
        from ._theorems_ import (transitivitySubsetEqSubset,
                                 transitivitySubsetEqSubsetEq)
        other = asExpression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.applyTransitivity(
                    self, other, assumptions=assumptions)
        if isinstance(other, ProperSuperset) or isinstance(other ,SupersetEq):
            other = other.deriveReversed(assumptions=assumptions)
            other = asExpression(other)
        if other.lhs == self.rhs:
            if isinstance(other, ProperSubset):
                return transitivitySubsetEqSubset.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
            elif isinstance(other,SubsetEq):
                return transitivitySubsetEqSubsetEq.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other, ProperSubset):
                return transitivitySubsetEqSubset.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
            elif isinstance(other,SubsetEq):
                return transitivitySubsetEqSubsetEq.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
        else:
            raise ValueError(
                    "Cannot perform transitivity with {0} and {1}!".
                    format(self, other))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this SubsetEq statement is
        in the Boolean set.
        '''
        from ._theorems_ import subsetEqInBool
        return subsetEqInBool.instantiate({A:self.lhs, B:self.rhs})

class NotSubsetEq(Operation):
    # operator of the NotSubsetEq operation
    _operator_ = Literal(stringFormat='nsubseteq', latexFormat=r'\nsubseteq',
                         theory=__file__)

    def __init__(self, subset, superset):
        Operation.__init__(self, NotSubsetEq._operator_, (subset, superset))

    def deriveSideEffects(self, judgment):
        # unfold as an automatic side-effect
        self.unfold(judgment.assumptions)

    def conclude(self, assumptions):
        return self.concludeAsFolded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsubseteq B, derive and return not(supseteq(A, B)).
        '''
        from ._theorems_ import unfoldNotSubsetEq
        return unfoldNotSubsetEq.instantiate(
            {A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded
        version, not(A supset B).
        '''
        from ._theorems_ import foldNotSubsetEq
        return foldNotSubsetEq.instantiate(
            {A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this NotSubsetEq statement is in the
        Boolean set. NOTE that the NotSubsetEq class has been
        created as an Operation and thus has operands instead of lhs
        and rhs attributes.
        '''
        from ._theorems_ import notSubsetEqInBool
        return notSubsetEqInBool.instantiate(
                {A:self.operands[0],B:self.operands[1]})

class ProperSubset(SubsetRelation):
    '''
    Class to represent proper subset relation, such as
    A proper_subset B, to represent the claim that any element in
    set A is also in set B, while B also has at least one element
    not in set A. Example usage: ProperSubset(A, B).
    Intended to replace the equivalent but more ambiguously-named
    Subset class.
    '''
    # operator of the Subset operation
    _operator_ = Literal(stringFormat='proper_subset', latexFormat=r'\subset',
                         theory=__file__)

    # map left-hand-sides to ProperSubset Judgments
    #   (populated in TransitivityRelation.sideEffects)
    knownLeftSides = dict()
    # map right-hand-sides to ProperSubset Judgments
    #   (populated in TransitivityRelation.sideEffects)
    knownRightSides = dict()

    def __init__(self, subset, superset):
        SubsetRelation.__init__(self, ProperSubset._operator_, subset, superset)
    
    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A not_proper_subset B, derive and return
        not(propersubset(A, B)).
        '''
        from ._theorems_ import unfoldProperSubset
        return unfoldProperSubset.instantiate(
            {A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)
    
    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From ProperSubset(A, B), derive ProperSuperset(B, A).
        '''
        from ._theorems_ import reverseProperSubset
        return reverseProperSubset.instantiate({A:self.subset, B:self.superset},
                                              assumptions=assumptions)

    def deriveRelaxed(self, assumptions=USE_DEFAULTS):
        '''
        From ProperSubset(A, B), derive SubsetEq(A, B).
        '''
        from ._theorems_ import relaxProperSubset
        return relaxProperSubset.instantiate({A:self.subset, B:self.superset},
                                            assumptions=assumptions)
    
    def deriveSupersetMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subset B and x in A, derive x in B.
        '''
        from ._theorems_ import supersetMembershipFromProperSubset
        return supersetMembershipFromProperSubset.instantiate(
                {A:self.subset, B:self.superset, x:element},
                assumptions=assumptions)

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this ProperSubset(A, B)
        expression and something of the form SubsetEq(B, C),
        ProperSubset(B, C), or B=C, to obtain ProperSubset(A, C) as
        appropriate.
        '''
        from proveit.logic import (
                Equals, ProperSubset, ProperSuperset, SubsetEq, SupersetEq)
        from ._theorems_ import (
                transitivitySubsetSubset, transitivitySubsetSubsetEq,)
        if isinstance(other, Equals):
            return ContainmentRelation.applyTransitivity(
                    self, other, assumptions=assumptions)
        if isinstance(other, ProperSuperset) or isinstance(other,SupersetEq):
            other = other.deriveReversed(assumptions=assumptions)
            other = asExpression(other)
        if other.lhs == self.rhs:
            if isinstance(other, ProperSubset):
                result = transitivitySubsetSubset.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result#.checked({self})
            elif isinstance(other, SubsetEq):
                result = transitivitySubsetSubsetEq.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other, ProperSubset):
                result = transitivitySubsetSubset.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
            elif isinstance(other,SubsetEq):
                result = transitivitySubsetSubsetEq.instantiate(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
        else:
            raise ValueError(
                    "Cannot perform transitivity with {0} and {1}!".
                    format(self, other))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this ProperSubset expression
        is in the Boolean set.
        '''
        from ._theorems_ import properSubsetInBool
        return properSubsetInBool.instantiate({A:self.lhs, B:self.rhs})

class NotProperSubset(Operation):
    # operator for the NotProperSubset operation
    _operator_ = Literal(stringFormat='not_proper_subset',
                         latexFormat=r'\not\subset',
                         theory=__file__)

    def __init__(self, subset, superset):
        Operation.__init__(self, NotProperSubset._operator_, (subset, superset))

    def deriveSideEffects(self, judgment):
        # unfold as an automatic side-effect
        self.unfold(judgment.assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        return self.concludeAsFolded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A not_proper_subset B, derive and return
        not(propersubset(A, B)).
        '''
        from ._theorems_ import unfoldNotProperSubset
        return unfoldNotProperSubset.instantiate(
            {A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A not_proper_subset B, from the
        unfolded version, not(A propersubset B).
        '''
        from ._theorems_ import foldNotProperSubset
        return foldNotProperSubset.instantiate(
            {A:self.operands[0], B:self.operands[1]}, assumptions=assumptions)

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this NotProperSubset statement is in the
        Boolean set. NOTE that the NotProperSubset class has been
        created as an Operation and thus has operands instead of lhs
        and rhs attributes.
        '''
        from ._theorems_ import notProperSubsetInBool
        return notProperSubsetInBool.instantiate(
                {A:self.operands[0],B:self.operands[1]})

# Provide aliases for ProperSubset to augment user's ease-of-use
SubsetProper = ProperSubset
StrictSubset = ProperSubset
