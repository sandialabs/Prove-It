from proveit import (
    as_expression, Literal, Operation, safe_dummy_var, USE_DEFAULTS)
from proveit._common_ import A, B, C, x
from .containment_relation import (
    ContainmentRelation, ContainmentSequence, make_sequence_or_relation)


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
        return ProperSuperset

    @staticmethod
    def SequenceClass():
        return SupersetSequence


class SupersetSequence(ContainmentSequence):
    def __init__(self, operators, operands):
        ContainmentSequence.__init__(self, operators, operands)

    @staticmethod
    def RelationClass():
        return SupersetRelation


def superset_sequence(operators, operands):
    '''
    Create a SupersetSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    return make_sequence_or_relation(SupersetSequence, operators, operands)


class SupersetEq(SupersetRelation):
    # operator of the SupersetEq operation
    _operator_ = Literal(string_format='supseteq', latex_format=r'\supseteq',
                         theory=__file__)

    # map left-hand-sides to SupersetEq Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to SupersetEq Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, superset, subset):
        SupersetRelation.__init__(
            self, SupersetEq._operator_, superset, subset)

    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From A supseteq B, derive B subseteq A.
        '''
        from ._theorems_ import reverse_supset_eq
        return reverse_supset_eq.instantiate(
            {A: self.superset, B: self.subset}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit import ProofFailure
        from proveit.logic import Equals

        # Any set contains itself
        try:
            Equals(*self.operands).prove(assumptions, automation=False)
            return self.conclude_via_equality(assumptions)
        except ProofFailure:
            pass

        try:
            # Attempt a transitivity search
            return ContainmentRelation.conclude(self, assumptions)
        except ProofFailure:
            pass  # transitivity search failed

        # Finally, attempt to conclude A supseteq B via
        # forall_{x in B} x in A.
        return self.conclude_as_folded(
            elem_instance_var=safe_dummy_var(self), assumptions=assumptions)

    def conclude_via_equality(self, assumptions=USE_DEFAULTS):
        from ._theorems_ import superset_eq_via_equality
        return superset_eq_via_equality.instantiate(
            {A: self.operands[0], B: self.operands[1]},
            assumptions=assumptions)

    # def unfold(self, elem_instance_var=x, assumptions=USE_DEFAULTS):
        '''
        From A superseteq B, derive and return (forall_{x in B} x in A).
        x will be relabeled if an elem_instance_var is supplied.
        '''
    #     from ._theorems_ import unfold_supset_eq
    # return unfold_supset_eq.instantiate({A:self.superset, B:self.subset,
    # x:elem_instance_var}, assumptions=assumptions)

    def unfold(self, elem_instance_var=None, assumptions=USE_DEFAULTS):
        '''
        From A superseteq B, derive and return (forall_{x in B} x in A).
        x will be relabeled if an elem_instance_var is supplied.
        '''
        from ._theorems_ import unfold_supset_eq
        if elem_instance_var is not None:
            temp_result = unfold_supset_eq.instantiate(
                {A: self.superset, B: self.subset}, assumptions=assumptions)
            return temp_result.instantiate(
                {x: elem_instance_var}, num_forall_eliminations=0, assumptions=assumptions)
        return unfold_supset_eq.instantiate(
            {A: self.superset, B: self.subset}, assumptions=assumptions)

    def derive_superset_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A superseteq B and x in B, derive x in A.
        '''
        from ._theorems_ import unfold_supset_eq
        _A, _B, _x = self.superset, self.subset, element
        return unfold_supset_eq.instantiate(
            {A: _A, B: _B, x: _x}, assumptions=assumptions)

    def derive_subset_nonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A superseteq B and element x not in A, derive x not in B.
        '''
        from ._theorems_ import refined_nonmembership
        _A, _B, _x = self.superset, self.subset, element
        return refined_nonmembership.instantiate({A: _A, B: _B, x: _x},
                                                 assumptions=assumptions)

    def conclude_as_folded(
            self,
            elem_instance_var=x,
            assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A superset B, from the unfolded
        version, (forall_{x in B} x in A).
        '''
        from ._theorems_ import fold_supset_eq
        return fold_supset_eq.instantiate(
            {A: self.superset, B: self.subset, x: elem_instance_var}, assumptions=assumptions)

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this SupersetEq(A, B)
        expression and something of the form SupersetEq(B, C),
        ProperSuperset(B, C), ProperSubset(C, B), SubsetEq(C, B),
        or B=C to obtain Superset(A, C) or SupersetEq(A, C) as
        appropriate. For example, calling
             SupersetEq(A,B).apply_transitivity(Equals(B,C),
                     assumptions=[SupersetEq(A,B), Equals(B,C)])
        returns:
             {SupersetEq(A,B), Equals(B,C)} |– SupersetEq(A,C)
        '''
        from proveit.logic import Equals
        from ._theorems_ import (
            transitivity_supset_eq_supset, transitivity_supset_eq_supset_eq)
        from .subset import ProperSubset, SubsetEq
        other = as_expression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.apply_transitivity(
                self, other, assumptions=assumptions)
        if (isinstance(other, ProperSubset) or isinstance(other, SubsetEq)):
            other = other.derive_reversed(assumptions=assumptions)
            other = as_expression(other)
        if other.lhs == self.rhs:
            if isinstance(other, ProperSuperset):
                result = transitivity_supset_eq_supset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
                return result
            elif isinstance(other, SupersetEq):
                result = transitivity_supset_eq_supset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other, ProperSuperset):
                result = transitivity_supset_eq_supset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
                return result
            elif isinstance(other, SupersetEq):
                result = transitivity_supset_eq_supset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
                return result
        else:
            raise ValueError("Cannot perform transitivity with "
                             "%s and %s!" % (self, other))

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this SupersetEq expression
        is in the Boolean set.
        '''
        from ._theorems_ import supset_eq_is_bool
        return supset_eq_is_bool.instantiate({A: self.lhs, B: self.rhs})


class NotSupersetEq(Operation):
    # operator of the NotSupersetEq operation
    _operator_ = Literal(string_format='nsupseteq',
                         latex_format=r'\nsupseteq',
                         theory=__file__)

    def __init__(self, superset, subset):
        Operation.__init__(self, NotSupersetEq._operator_, (superset, subset))

    def derive_side_effects(self, judgment):
        # unfold as an automatic side-effect
        self.unfold(judgment.assumptions)

    def conclude(self, assumptions):
        return self.conclude_as_folded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsupseteq B, derive and return not(supseteq(A, B)).
        '''
        from ._theorems_ import unfold_not_supset_eq
        return unfold_not_supset_eq.instantiate(
            {A: self.operands[0], B: self.operands[1]},
            assumptions=assumptions)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded
        version, not(A supset B).
        '''
        from ._theorems_ import fold_not_supset_eq
        return fold_not_supset_eq.instantiate(
            {A: self.operands[0], B: self.operands[1]},
            assumptions=assumptions)


class ProperSuperset(SupersetRelation):
    # operator of the ProperSuperset operation
    _operator_ = Literal(
        string_format='proper_superset',
        latex_format=r'\supset',
        theory=__file__)

    # map left-hand-sides to ProperSuperset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to Superset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, superset, subset):
        SupersetRelation.__init__(self, ProperSuperset._operator_,
                                  superset, subset)

    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From A proper_superset B, derive B proper_subset A.
        '''
        from ._theorems_ import reverse_proper_superset
        return reverse_proper_superset.instantiate(
            {A: self.superset, B: self.subset}, assumptions=assumptions)

    def derive_relaxed(self, assumptions=USE_DEFAULTS):
        '''
        From A proper_superset B, derive A supseteq B.
        '''
        from ._theorems_ import relax_proper_superset
        return relax_proper_superset.instantiate(
            {A: self.superset, B: self.subset}, assumptions=assumptions)

    def derive_superset_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A supset B and x in B, derive x in A.
        '''
        from ._theorems_ import superset_membership_from_proper_superset
        return superset_membership_from_proper_superset.instantiate(
            {A: self.subset, B: self.superset, x: element},
            assumptions=assumptions)

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this
        ProperSuperset(A, B) expression and something of the form
        SupersetEq(B, C), ProperSuperset(B, C), ProperSubset(C, B),
        SubsetEq(C, B), or B=C to obtain ProperSuperset(A, C) or
        SupersetEq(A, C) as appropriate. For example, calling
             ProperSuperset(A,B).apply_transitivity(Equals(B,C),
                     assumptions=[ProperSuperset(A,B), Equals(B,C)])
        returns:
             {ProperSuperset(A,B), Equals(B,C)} |– ProperSuperset(A,C)
        '''
        from proveit.logic import (
            Equals, ProperSubset, SubsetEq)
        from ._theorems_ import (
            transitivity_supset_supset, transitivity_supset_supset_eq)
        other = as_expression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.apply_transitivity(
                self, other, assumptions=assumptions)
        if isinstance(other, ProperSubset) or isinstance(other, SubsetEq):
            other = other.derive_reversed(assumptions=assumptions)
            other = as_expression(other)
        if other.lhs == self.rhs:
            if isinstance(other, ProperSuperset):
                result = transitivity_supset_supset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
                return result
            elif isinstance(other, SupersetEq):
                result = transitivity_supset_supset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other, ProperSuperset):
                result = transitivity_supset_supset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
                return result
            elif isinstance(other, SupersetEq):
                result = transitivity_supset_supset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
                return result
        else:
            raise ValueError("Cannot perform transitivity with "
                             "%s and %s!" % (self, other))

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this ProperSuperset expression
        is in the Boolean set.
        '''
        from ._theorems_ import proper_supset_is_bool
        return proper_supset_is_bool.instantiate({A: self.lhs, B: self.rhs})


class NotProperSuperset(Operation):

    # operator of the NotProperSuperset operation
    _operator_ = Literal(string_format='nsupset',
                         latex_format=r'\not\supset',
                         theory=__file__)

    def __init__(self, superset, subset):
        Operation.__init__(self, NotProperSuperset._operator_,
                           (superset, subset))

    def derive_side_effects(self, judgment):
        # unfold as an automatic side-effect
        self.unfold(judgment.assumptions)

    def conclude(self, assumptions):
        return self.conclude_as_folded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A npropersupset B, derive and return
        not(propersupset(A, B)).
        '''
        from ._theorems_ import unfold_not_proper_supset
        return unfold_not_proper_supset.instantiate(
            {A: self.operands[0], B: self.operands[1]},
            assumptions=assumptions)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A npropersupset B, from the
        unfolded version, not(A propersupset B).
        '''
        from ._theorems_ import fold_not_proper_supset
        return fold_not_proper_supset.instantiate(
            {A: self.operands[0], B: self.operands[1]},
            assumptions=assumptions)


# Provide aliases for ProperSuperset to augment user's ease-of-use
SupersetProper = ProperSuperset
StrictSuperset = ProperSuperset
