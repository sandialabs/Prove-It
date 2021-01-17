from proveit import (as_expression, Literal, Operation, safe_dummy_var,
                     USE_DEFAULTS)
from proveit import A, B, C, Q, x
from proveit import S
from .inclusion_relation import InclusionRelation


class SubsetEq(InclusionRelation):
    # operator of the SubsetEq operation
    _operator_ = Literal(string_format='subset_eq', latex_format=r'\subseteq',
                         theory=__file__)

    # map left-hand-sides to SubsetEq Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to SubsetEq Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, A, B):
        '''
        Create the expression for (A subset_eq B)
        '''
        InclusionRelation.__init__(self, SubsetEq._operator_, A, B)

    @staticmethod
    def reversed_operator_str(format_type):
        '''
        Reversing subset_eq gives superset_eq.
        '''
        return r'\supseteq' if format_type == 'latex' else 'superset_eq'

    def remake_constructor(self):
        if self.is_reversed():
            # Use the 'superset_eq' function if it is reversed.
            return 'superset_eq'
        # Use the default.
        return Operation.remake_constructor(self)
    
    def conclude(self, assumptions=USE_DEFAULTS):
        from proveit import ProofFailure
        from proveit.logic import Equals, SetOfAll, SetEquiv

        # Equal sets include each other.
        if Equals(*self.operands.entries).proven(assumptions):
            return self.conclude_via_equality(assumptions)

        # Equivalent sets include each other.
        if SetEquiv(*self.operands.entries).proven(assumptions):
            return self.conclude_via_equivalence(assumptions)

        # Check for special case of set comprehension
        # [{x | Q*(x)}_{x \in S}] \subseteq S
        if isinstance(self.subset, SetOfAll):
            from proveit.logic.sets.comprehension import (
                comprehension_is_subset)
            set_of_all = self.subset
            if (len(set_of_all.all_instance_vars()) == 1 and
                set_of_all.instance_element == set_of_all.all_instance_vars()[0] and
                    set_of_all.domain == self.superset):
                Q_op, Q_op_sub = (
                    Operation(Q, set_of_all.all_instance_vars()),
                    set_of_all.conditions)
                concluded = comprehension_is_subset.instantiate(
                    {S: set_of_all.domain, Q_op: Q_op_sub},
                    relabel_map={x: set_of_all.all_instance_vars()[0]},
                    assumptions=assumptions)
                return concluded.with_matching_style(self)

        _A, _B = self.operands.entries
        if hasattr(_B, 'deduce_subset_eq_relation'):
            try:
                return _B.deduce_subset_eq_relation(_A, assumptions)
            except NotImplementedError:
                pass

        try:
            # Attempt to conclude A subseteq B via
            # forall_{x in A} x in B.
            return self.conclude_as_folded(
                elem_instance_var=safe_dummy_var(self), assumptions=assumptions)
        except ProofFailure as e:
            raise ProofFailure(self, assumptions,
                           "Failed to conclude as folded: %s.\n"
                           "To try to prove %s via transitive "
                           "relations, try 'conclude_via_transitivity'."
                           %(str(self), str(e)))

    def conclude_via_equality(self, assumptions=USE_DEFAULTS):
        from . import subset_eq_via_equality
        concluded = subset_eq_via_equality.instantiate(
            {A: self.subset, B: self.superset},
            assumptions=assumptions)
        return concluded.with_matching_style(self)

    def conclude_via_equivalence(self, assumptions=USE_DEFAULTS):
        from . import subset_eq_via_equivalence
        concluded = subset_eq_via_equivalence.instantiate(
            {A: self.subset, B: self.superset},
            assumptions=assumptions)
        return concluded.with_matching_style(self)

    def conclude_as_folded(
            self,
            elem_instance_var=x,
            assumptions=USE_DEFAULTS):
        '''
        Derive this folded version, A subseteq B, from the unfolded
        version, (forall_{x in A} x in B).
        '''
        from . import fold_subset_eq
        concluded = fold_subset_eq.instantiate(
            {A: self.subset, B: self.superset, x: elem_instance_var}, 
            assumptions=assumptions)
        return concluded.with_matching_style(self)
    
    def unfold(self, elem_instance_var=None, assumptions=USE_DEFAULTS):
        '''
        From A subset_eq B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elem_instance_var is supplied.
        '''
        from . import unfold_subset_eq
        if elem_instance_var is not None:
            temp_result = unfold_subset_eq.instantiate(
                {A: self.subset, B: self.superset}, assumptions=assumptions)
            return temp_result.instantiate(
                {x: elem_instance_var}, num_forall_eliminations=0, 
                assumptions=assumptions)
        return unfold_subset_eq.instantiate(
            {A: self.subset, B: self.superset}, assumptions=assumptions)

    def derive_superset_membership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subset_eq B and element x in A, derive x in B.
        '''
        from . import unfold_subset_eq
        return unfold_subset_eq.instantiate(
            {A: self.subset, B: self.superset, x: element},
            assumptions=assumptions)

    def derive_subset_nonmembership(self, element, assumptions=USE_DEFAULTS):
        '''
        From A subset_eq B and element x not_in B, derive x in A.
        '''
        from . import refined_nonmembership
        return refined_nonmembership.instantiate(
            {A: self.subset, B: self.superset, x: element},
            assumptions=assumptions)
    
    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply a transitivity rule to derive from this A subseteq B
        expression and something of the form B subseteq C, B subset C,
        or B=C to obtain A subset B or A subseteq B as appropriate.
        '''
        from proveit.logic import Equals, SetEquiv, ProperSubset
        from . import (transitivity_subset_eq_subset,
                       transitivity_subset_subset_eq,
                       transitivity_subset_eq_subset_eq)
        other = as_expression(other)
        if isinstance(other, Equals) or isinstance(other, SetEquiv):
            return InclusionRelation.apply_transitivity(
                self, other, assumptions=assumptions)
        if other.subset == self.superset:
            if isinstance(other, ProperSubset):
                new_rel = transitivity_subset_eq_subset.instantiate(
                    {A: self.subset, B: self.superset, C: other.superset},
                    assumptions=assumptions)
            elif isinstance(other, SubsetEq):
                new_rel = transitivity_subset_eq_subset_eq.instantiate(
                    {A: self.subset, B: self.superset, C: other.superset},
                    assumptions=assumptions)
        elif other.superset == self.subset:
            if isinstance(other, ProperSubset):
                new_rel = transitivity_subset_subset_eq.instantiate(
                    {A: other.subset, B: other.superset, C: self.superset},
                    assumptions=assumptions)
            elif isinstance(other, SubsetEq):
                new_rel = transitivity_subset_eq_subset_eq.instantiate(
                    {A: other.subset, B: other.superset, C: self.superset},
                    assumptions=assumptions)
        else:
            raise ValueError(
                "Cannot perform transitivity with {0} and {1}!".
                format(self, other))
        return new_rel.with_mimicked_style(self)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this SubsetEq statement is
        in the Boolean set.
        '''
        from . import subset_eq_is_bool
        is_bool_stmt = subset_eq_is_bool.instantiate(
                {A: self.normal_lhs, B: self.normal_rhs}, 
                assumptions=assumptions)
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

def superset_eq(A, B):
    '''
    Return the expression representing (A superset_eq B), internally
    represented as (B subset_eq A) but with a style that reverses
    the direction.
    '''
    return SubsetEq(B, A).with_styles(direction = 'reversed')
