from proveit import (as_expression, Literal, Operation, safe_dummy_var,
                     USE_DEFAULTS)
from proveit import A, B, C, x
from proveit import f, S
from .containment_relation import (
    ContainmentRelation, ContainmentSequence, make_sequence_or_relation)


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


def subset_sequence(operators, operands):
    '''
    Create a SubsetSequence with the given operators or operands,
    or create an appropriate degenerate Expression when there are
    fewer than two operators.
    '''
    return make_sequence_or_relation(SubsetSequence, operators, operands)


class SubsetEq(SubsetRelation):
    # operator of the SubsetEq operation
    _operator_ = Literal(string_format='subseteq', latex_format=r'\subseteq',
                         theory=__file__)

    # map left-hand-sides to SubsetEq Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to SubsetEq Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, subset, superset):
        SubsetRelation.__init__(self, SubsetEq._operator_, subset, superset)

    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B, derive B supseteq A.
        '''
        from . import reverse_subset_eq
        return reverse_subset_eq.instantiate(
            {A: self.subset, B: self.superset}, assumptions=assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit import ProofFailure
        from proveit.logic import SetOfAll, Equals

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

        # Check for special case of [{x | Q*(x)}_{x \in S}] \subseteq S
        if isinstance(self.subset, SetOfAll):
            from proveit.logic.sets.comprehension import (
                comprehension_is_subset)
            set_of_all = self.subset
            if (len(set_of_all.all_instance_vars()) == 1 and
                set_of_all.instance_element == set_of_all.all_instance_vars()[0] and
                    set_of_all.domain == self.superset):
                Q_op, Q_op_sub = (
                    Operation(QQ, set_of_all.all_instance_vars()),
                    set_of_all.conditions)
                return comprehension_is_subset.instantiate(
                    {S: set_of_all.domain, Q_op: Q_op_sub},
                    relabel_map={x: set_of_all.all_instance_vars()[0]},
                    assumptions=assumptions)

        # Finally, attempt to conclude A subseteq B via
        # forall_{x in A} x in B. Issue: Variables do not match when
        # using safe_dummy_var: _x_ to x.
        # We need to automate this better; right now it is only
        # practical to do conclude_as_folded manually.
        return self.conclude_as_folded(
            elem_instance_var=safe_dummy_var(self), assumptions=assumptions)

    def conclude_via_equality(self, assumptions=USE_DEFAULTS):
        from . import subset_eq_via_equality
        return subset_eq_via_equality.instantiate(
            {A: self.operands[0], B: self.operands[1]},
            assumptions=assumptions)

    def unfold(self, elem_instance_var=None, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elem_instance_var is supplied.
        '''
        from . import unfold_subset_eq
        if elem_instance_var is not None:
            temp_result = unfold_subset_eq.instantiate(
                {A: self.subset, B: self.superset}, assumptions=assumptions)
            return temp_result.instantiate(
                {x: elem_instance_var}, num_forall_eliminations=0, assumptions=assumptions)
        return unfold_subset_eq.instantiate(
            {A: self.subset, B: self.superset}, assumptions=assumptions)

    def derive_superset_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subseteq B and element x in A, derive x in B.
        '''
        from . import unfold_subset_eq
        return unfold_subset_eq.instantiate(
            {A: self.subset, B: self.superset, x: element},
            assumptions=assumptions)

    def conclude_as_folded(
            self,
            elem_instance_var=x,
            assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A subseteq B, from the unfolded
        version, (forall_{x in A} x in B).
        '''
        from . import fold_subset_eq
        return fold_subset_eq.instantiate(
            {A: self.subset, B: self.superset, x: elem_instance_var}, assumptions=assumptions)

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this A subseteq B
        expression and something of the form B subseteq C, B subset C,
        or B=C to obtain A subset B or A subseteq B as appropriate.
        '''
        from proveit.logic import (
            Equals, ProperSubset, ProperSuperset, SubsetEq, SupersetEq)
        from . import (transitivity_subset_eq_subset,
                                 transitivity_subset_eq_subset_eq)
        other = as_expression(other)
        if isinstance(other, Equals):
            return ContainmentRelation.apply_transitivity(
                self, other, assumptions=assumptions)
        if isinstance(other, ProperSuperset) or isinstance(other, SupersetEq):
            other = other.derive_reversed(assumptions=assumptions)
            other = as_expression(other)
        if other.lhs == self.rhs:
            if isinstance(other, ProperSubset):
                return transitivity_subset_eq_subset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
            elif isinstance(other, SubsetEq):
                return transitivity_subset_eq_subset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
        elif other.rhs == self.lhs:
            if isinstance(other, ProperSubset):
                return transitivity_subset_eq_subset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
            elif isinstance(other, SubsetEq):
                return transitivity_subset_eq_subset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
        else:
            raise ValueError(
                "Cannot perform transitivity with {0} and {1}!".
                format(self, other))

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this SubsetEq statement is
        in the Boolean set.
        '''
        from . import subset_eq_is_bool
        return subset_eq_is_bool.instantiate({A: self.lhs, B: self.rhs})


class NotSubsetEq(Operation):
    # operator of the NotSubsetEq operation
    _operator_ = Literal(string_format='nsubseteq', latex_format=r'\nsubseteq',
                         theory=__file__)

    def __init__(self, subset, superset):
        Operation.__init__(self, NotSubsetEq._operator_, (subset, superset))

    def derive_side_effects(self, judgment):
        # unfold as an automatic side-effect
        self.unfold(judgment.assumptions)

    def conclude(self, assumptions):
        return self.conclude_as_folded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A nsubseteq B, derive and return not(supseteq(A, B)).
        '''
        from . import unfold_not_subset_eq
        return unfold_not_subset_eq.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A nsupset B, from the unfolded
        version, not(A supset B).
        '''
        from . import fold_not_subset_eq
        return fold_not_subset_eq.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this NotSubsetEq statement is in the
        Boolean set. NOTE that the NotSubsetEq class has been
        created as an Operation and thus has operands instead of lhs
        and rhs attributes.
        '''
        from . import not_subset_eq_is_bool
        return not_subset_eq_is_bool.instantiate(
            {A: self.operands[0], B: self.operands[1]})


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
    _operator_ = Literal(
        string_format='proper_subset',
        latex_format=r'\subset',
        theory=__file__)

    # map left-hand-sides to ProperSubset Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_left_sides = dict()
    # map right-hand-sides to ProperSubset Judgments
    #   (populated in TransitivityRelation.side_effects)
    known_right_sides = dict()

    def __init__(self, subset, superset):
        SubsetRelation.__init__(
            self, ProperSubset._operator_, subset, superset)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A not_proper_subset B, derive and return
        not(propersubset(A, B)).
        '''
        from . import unfold_proper_subset
        return unfold_proper_subset.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From ProperSubset(A, B), derive ProperSuperset(B, A).
        '''
        from . import reverse_proper_subset
        return reverse_proper_subset.instantiate(
            {A: self.subset, B: self.superset}, assumptions=assumptions)

    def derive_relaxed(self, assumptions=USE_DEFAULTS):
        '''
        From ProperSubset(A, B), derive SubsetEq(A, B).
        '''
        from . import relax_proper_subset
        return relax_proper_subset.instantiate(
            {A: self.subset, B: self.superset}, assumptions=assumptions)

    def derive_superset_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subset B and x in A, derive x in B.
        '''
        from . import superset_membership_from_proper_subset
        return superset_membership_from_proper_subset.instantiate(
            {A: self.subset, B: self.superset, x: element},
            assumptions=assumptions)

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this ProperSubset(A, B)
        expression and something of the form SubsetEq(B, C),
        ProperSubset(B, C), or B=C, to obtain ProperSubset(A, C) as
        appropriate.
        '''
        from proveit.logic import (
            Equals, ProperSubset, ProperSuperset, SubsetEq, SupersetEq)
        from . import (
            transitivity_subset_subset, transitivity_subset_subset_eq,)
        if isinstance(other, Equals):
            return ContainmentRelation.apply_transitivity(
                self, other, assumptions=assumptions)
        if isinstance(other, ProperSuperset) or isinstance(other, SupersetEq):
            other = other.derive_reversed(assumptions=assumptions)
            other = as_expression(other)
        if other.lhs == self.rhs:
            if isinstance(other, ProperSubset):
                result = transitivity_subset_subset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
                return result  # .checked({self})
            elif isinstance(other, SubsetEq):
                result = transitivity_subset_subset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.rhs},
                    assumptions=assumptions)
                return result
        elif other.rhs == self.lhs:
            if isinstance(other, ProperSubset):
                result = transitivity_subset_subset.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
                return result
            elif isinstance(other, SubsetEq):
                result = transitivity_subset_subset_eq.instantiate(
                    {A: self.lhs, B: self.rhs, C: other.lhs},
                    assumptions=assumptions)
                return result
        else:
            raise ValueError(
                "Cannot perform transitivity with {0} and {1}!".
                format(self, other))

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this ProperSubset expression
        is in the Boolean set.
        '''
        from . import proper_subset_is_bool
        return proper_subset_is_bool.instantiate({A: self.lhs, B: self.rhs})


class NotProperSubset(Operation):
    # operator for the NotProperSubset operation
    _operator_ = Literal(string_format='not_proper_subset',
                         latex_format=r'\not\subset',
                         theory=__file__)

    def __init__(self, subset, superset):
        Operation.__init__(
            self, NotProperSubset._operator_, (subset, superset))

    def derive_side_effects(self, judgment):
        # unfold as an automatic side-effect
        self.unfold(judgment.assumptions)

    def conclude(self, assumptions=USE_DEFAULTS):
        return self.conclude_as_folded(assumptions)

    def unfold(self, assumptions=USE_DEFAULTS):
        '''
        From A not_proper_subset B, derive and return
        not(propersubset(A, B)).
        '''
        from . import unfold_not_proper_subset
        return unfold_not_proper_subset.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A not_proper_subset B, from the
        unfolded version, not(A propersubset B).
        '''
        from . import fold_not_proper_subset
        return fold_not_proper_subset.instantiate(
            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this NotProperSubset statement is in the
        Boolean set. NOTE that the NotProperSubset class has been
        created as an Operation and thus has operands instead of lhs
        and rhs attributes.
        '''
        from . import not_proper_subset_is_bool
        return not_proper_subset_is_bool.instantiate(
            {A: self.operands[0], B: self.operands[1]})


# Provide aliases for ProperSubset to augment user's ease-of-use
SubsetProper = ProperSubset
StrictSubset = ProperSubset
