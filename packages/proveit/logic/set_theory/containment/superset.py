from proveit import (
        asExpression, Literal, Operation, safeDummyVar, USE_DEFAULTS)
from proveit._common_ import A, B, C, x
from .containment_relation import (
        ContainmentRelation, ContainmentSequence, makeSequenceOrRelation)

class SupersetRelation(ContainmentRelation):
    def __init__(self, operator, superset, subset):
        ContainmentRelation.__init__(self, operator, superset, subset)
        self.superset = self.operands[0]
        self.subset = self.operands[1]

    @staticmethod
    def WeakRelationClass():
        return SupersetEq

    @staticmethod
    def StrongRelationClass():
        return Superset

    @staticmethod
    def SequenceClass():
        return SupersetSequence

class SupersetSequence(ContainmentSequence):
    def __init__(self, operators, operands):
        ContainmentSequence.__init__(self, operators, operands)

    @staticmethod
    def RelationClass():
        return SupersetRelation

def supersetSequence(operators, operands):
    '''
    Create a SupersetSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    return makeSequenceOrRelation(SupersetSequence, operators, operands)

class Superset(SupersetRelation):
    # operator of the Superset operation
    _operator_ = Literal(stringFormat='supset', latexFormat=r'\supset',
                         context=__file__)

    # map left-hand-sides to Superset KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()
    # map right-hand-sides to Superset KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()

    def __init__(self, superset, subset):
        SupersetRelation.__init__(self, Superset._operator_, superset, subset)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A subset B, derive B supset A.
        '''
        from ._theorems_ import reverseSupset
        return reverseSupset.specialize(
                {A:self.superset, B:self.subset}, assumptions=assumptions)

    def deriveRelaxed(self, assumptions=USE_DEFAULTS):
        '''
        From A supset B, derive A supseteq B.
        '''
        from ._theorems_ import relaxSupset
        return relaxSupset.specialize(
                {A:self.superset, B:self.subset}, assumptions=assumptions)

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this Superset(A, B)
        expression and something of the form SupersetEq(B, C),
        ProperSuperset(B, C), ProperSubset(C, B), SubsetEq(C, B),
        or B=C to obtain ProperSuperset(A, C) or SupersetEq(A, C) as
        appropriate. For example, calling
             Superset(A,B).applyTransitivity(Equals(B,C),
                     assumptions=[Superset(A,B), Equals(B,C)])
        returns:
             {Superset(A,B), Equals(B,C)} |– Superset(A,C)
        '''
        from proveit.logic import Equals, ProperSubset, Subset, SubsetEq
        from ._theorems_ import (
                transitivitySupsetSupset, transitivitySupsetSupsetEq)
        other = asExpression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.applyTransitivity(
                    self, other, assumptions=assumptions)
        if (isinstance(other, Subset) or isinstance(other, ProperSubset)
            or isinstance(other,SubsetEq)):
            other = other.deriveReversed(assumptions=assumptions)
            other = asExpression(other)
        if other.lhs == self.rhs:
            if isinstance(other,Superset) or isinstance(other, ProperSuperset):
                result = transitivitySupsetSupset.specialize(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result
            elif isinstance(other,SupersetEq):
                result = transitivitySupsetSupsetEq.specialize(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,Superset) or isinstance(other, ProperSuperset):
                result = transitivitySupsetSupset.specialize(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
            elif isinstance(other,SupersetEq):
                result = transitivitySupsetSupsetEq.specialize(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
        else:
            raise ValueError("Cannot perform transitivity with "
                             "%s and %s!"%(self, other))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this Superset expression
        is in the set of Booleans.
        '''
        from ._theorems_ import supsetInBool
        return supsetInBool.specialize({A:self.lhs, B:self.rhs})

class ProperSuperset(SupersetRelation):
    # operator of the ProperSuperset operation
    _operator_ = Literal(stringFormat='proper_superset', latexFormat=r'\supset',
                         context=__file__)

    # map left-hand-sides to ProperSuperset KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()
    # map right-hand-sides to Superset KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()

    def __init__(self, superset, subset):
        SupersetRelation.__init__(self, ProperSuperset._operator_,
                                  superset, subset)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A proper_superset B, derive B proper_subset A.
        '''
        from ._theorems_ import reverseProperSuperset
        return reverseProperSuperset.specialize(
                {A:self.superset, B:self.subset}, assumptions=assumptions)

    def deriveRelaxed(self, assumptions=USE_DEFAULTS):
        '''
        From A proper_superset B, derive A supseteq B.
        '''
        from ._theorems_ import relaxProperSuperset
        return relaxProperSuperset.specialize(
                {A:self.superset, B:self.subset}, assumptions=assumptions)

    def deriveSupsersetMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A supset B and x in B, derive x in A.
        '''
        from ._theorems_ import supersetMembership
        return supersetMembership.instantiate(
                {A:self.subset, B:self.superset, x:element},
                assumptions=assumptions)

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this
        ProperSuperset(A, B) expression and something of the form
        SupersetEq(B, C), ProperSuperset(B, C), ProperSubset(C, B),
        SubsetEq(C, B), or B=C to obtain ProperSuperset(A, C) or
        SupersetEq(A, C) as appropriate. For example, calling
             ProperSuperset(A,B).applyTransitivity(Equals(B,C),
                     assumptions=[ProperSuperset(A,B), Equals(B,C)])
        returns:
             {ProperSuperset(A,B), Equals(B,C)} |– ProperSuperset(A,C)
        '''
        from proveit.logic import (
                Equals, ProperSubset, Subset, SubsetEq)
        from ._theorems_ import (
                transitivitySupsetSupset, transitivitySupsetSupsetEq)
        other = asExpression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.applyTransitivity(
                    self, other, assumptions=assumptions)
        if (isinstance(other, Subset) or isinstance(other, ProperSubset)
            or isinstance(other,SubsetEq)):
            other = other.deriveReversed(assumptions=assumptions)
            other = asExpression(other)
        if other.lhs == self.rhs:
            if isinstance(other,Superset) or isinstance(other, ProperSuperset):
                result = transitivitySupsetSupset.specialize(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result
            elif isinstance(other,SupersetEq):
                result = transitivitySupsetSupsetEq.specialize(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,Superset) or isinstance(other, ProperSuperset):
                result = transitivitySupsetSupset.specialize(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
            elif isinstance(other,SupersetEq):
                result = transitivitySupsetSupsetEq.specialize(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
        else:
            raise ValueError("Cannot perform transitivity with "
                             "%s and %s!"%(self, other))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this ProperSuperset expression
        is in the set of Booleans.
        '''
        from ._theorems_ import properSupsetInBool
        return properSupsetInBool.specialize({A:self.lhs, B:self.rhs})

class SupersetEq(SupersetRelation):
    # operator of the SupersetEq operation
    _operator_ = Literal(stringFormat='supseteq', latexFormat=r'\supseteq',
                         context=__file__)

    # map left-hand-sides to SupersetEq KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownLeftSides = dict()
    # map right-hand-sides to SupersetEq KnownTruths
    #   (populated in TransitivityRelation.deriveSideEffects)
    knownRightSides = dict()

    def __init__(self, superset, subset):
        SupersetRelation.__init__(self, SupersetEq._operator_, superset, subset)

    def deriveReversed(self, assumptions=USE_DEFAULTS):
        '''
        From A supseteq B, derive B subseteq A.
        '''
        from ._theorems_ import reverseSupsetEq
        return reverseSupsetEq.specialize(
                {A:self.superset, B:self.subset}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit import ProofFailure
        from proveit.logic import Equals

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

        # Finally, attempt to conclude A supseteq B via
        # forall_{x in B} x in A.
        return self.concludeAsFolded(
                elemInstanceVar=safeDummyVar(self), assumptions=assumptions)

    def concludeViaEquality(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import supersetEqViaEquality
        return supersetEqViaEquality.specialize(
                {A: self.operands[0], B: self.operands[1]},
                assumptions=assumptions)

    def unfold(self, elemInstanceVar=x, assumptions=USE_DEFAULTS):
        '''
        From A superseteq B, derive and return (forall_{x in B} x in A).
        x will be relabeled if an elemInstanceVar is supplied.
        '''
        from ._theorems_ import unfoldSupsetEq
        return unfoldSupsetEq.specialize({A:self.superset, B:self.subset, x:elemInstanceVar}, assumptions=assumptions)

    def deriveSupsersetMembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A superseteq B and x in B, derive x in A.
        '''
        from ._theorems_ import unfoldSupsetEq
        _A, _B, _x = self.superset, self.subset, self.element
        return unfoldSupsetEq.specialize({A:_A, B:_B, x:_x}, assumptions=assumptions)

    def deriveSubsetNonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A superseteq B and x not in A, derive x not in B.
        '''
        from ._theorems_ import refinedNonmembership
        _A, _B, _x = self.superset, self.subset, self.element
        return refinedNonmembership.specialize({A:_A, B:_B, x:_x},
                                               assumptions=assumptions)


    def concludeAsFolded(self, elemInstanceVar=x, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A superset B, from the unfolded
        version, (forall_{x in B} x in A).
        '''
        from ._theorems_ import foldSupsetEq
        return foldSupsetEq.specialize({A:self.superset, B:self.subset, x:elemInstanceVar}, assumptions=assumptions).deriveConsequent(assumptions)

    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this SupersetEq(A, B)
        expression and something of the form SupersetEq(B, C),
        ProperSuperset(B, C), ProperSubset(C, B), SubsetEq(C, B),
        or B=C to obtain Superset(A, C) or SupersetEq(A, C) as
        appropriate. For example, calling
             SupersetEq(A,B).applyTransitivity(Equals(B,C),
                     assumptions=[SupersetEq(A,B), Equals(B,C)])
        returns:
             {SupersetEq(A,B), Equals(B,C)} |– SupersetEq(A,C)
        '''
        from proveit.logic import Equals
        from ._theorems_ import (
                transitivitySupsetEqSupset, transitivitySupsetEqSupsetEq)
        from .subset import ProperSubset, Subset, SubsetEq
        other = asExpression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.applyTransitivity(
                    self, other, assumptions=assumptions)
        if (isinstance(other, Subset) or isinstance(other, ProperSubset)
            or isinstance(other,SubsetEq)):
            other = other.deriveReversed(assumptions=assumptions)
            other = asExpression(other)
        if other.lhs == self.rhs:
            if isinstance(other,Superset) or isinstance(other, ProperSuperset):
                result = transitivitySupsetEqSupset.specialize(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result
            elif isinstance(other,SupersetEq):
                result = transitivitySupsetEqSupsetEq.specialize(
                        {A:self.lhs, B:self.rhs, C:other.rhs},
                        assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other,Superset) or isinstance(other, ProperSuperset):
                result = transitivitySupsetEqSupset.specialize(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
            elif isinstance(other,SupersetEq):
                result = transitivitySupsetEqSupsetEq.specialize(
                        {A:self.lhs, B:self.rhs, C:other.lhs},
                        assumptions=assumptions)
                return result
        else:
            raise ValueError("Cannot perform transitivity with "
                             "%s and %s!"%(self, other))

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this SupersetEq expression
        is in the set of Booleans.
        '''
        from ._theorems_ import supsetEqInBool
        return supsetEqInBool.specialize({A:self.lhs, B:self.rhs})

class NotSuperset(Operation):

    # operator of the NotSuperset operation
    _operator_ = Literal(stringFormat='nsupset',
                         latexFormat=r'\not\supset',
                         context=__file__)

    def __init__(self, superset, subset):
        Operation.__init__(self, NotSuperset._operator_, (superset, subset))

    def deriveSideEffects(self, knownTruth):
        # unfold as an automatic side-effect
        self.unfold(knownTruth.assumptions)

    def conclude(self, assumptions):
        return self.concludeAsFolded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsupset B, derive and return not(supset(A, B)).
        '''
        from ._theorems_ import unfoldNotSupset
        return unfoldNotSupset.specialize(
                {A:self.operands[0], B:self.operands[1]},
                assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded
        version, not(A supset B).
        '''
        from ._theorems_ import foldNotSupset
        return foldNotSupset.specialize(
                {A:self.operands[0], B:self.operands[1]},
                assumptions=assumptions)

class NotProperSuperset(Operation):

    # operator of the NotProperSuperset operation
    _operator_ = Literal(stringFormat='nsupset',
                         latexFormat=r'\not\supset',
                         context=__file__)

    def __init__(self, superset, subset):
        Operation.__init__(self, NotProperSuperset._operator_,
                           (superset, subset))

    def deriveSideEffects(self, knownTruth):
        # unfold as an automatic side-effect
        self.unfold(knownTruth.assumptions)

    def conclude(self, assumptions):
        return self.concludeAsFolded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A npropersupset B, derive and return
        not(propersupset(A, B)).
        '''
        from ._theorems_ import unfoldNotProperSupset
        return unfoldNotProperSupset.specialize(
                {A:self.operands[0], B:self.operands[1]},
                assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A npropersupset B, from the
        unfolded version, not(A propersupset B).
        '''
        from ._theorems_ import foldNotProperSupset
        return foldNotProperSupset.specialize(
                {A:self.operands[0], B:self.operands[1]},
                assumptions=assumptions)

class NotSupersetEq(Operation):
    # operator of the NotSupersetEq operation
    _operator_ = Literal(stringFormat='nsupseteq',
                         latexFormat=r'\nsupseteq',
                         context=__file__)

    def __init__(self, superset, subset):
        Operation.__init__(self, NotSupersetEq._operator_, (superset, subset))

    def deriveSideEffects(self, knownTruth):
        # unfold as an automatic side-effect
        self.unfold(knownTruth.assumptions)

    def conclude(self, assumptions):
        return self.concludeAsFolded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsupseteq B, derive and return not(supseteq(A, B)).
        '''
        from ._theorems_ import unfoldNotSupsetEq
        return unfoldNotSupsetEq.specialize(
                {A:self.operands[0], B:self.operands[1]},
                assumptions=assumptions)

    def concludeAsFolded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded
        version, not(A supset B).
        '''
        from ._theorems_ import foldNotSupsetEq
        return foldNotSupsetEq.specialize(
                {A:self.operands[0], B:self.operands[1]},
                assumptions=assumptions)

# Provide aliases for ProperSuperset to augment user's ease-of-use
SupersetProper = ProperSuperset
StrictSuperset = ProperSuperset
