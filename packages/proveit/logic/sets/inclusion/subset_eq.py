from proveit import (as_expression, Function, Literal, Operation, 
                     free_vars, safe_dummy_var,
                     Judgment, UnsatisfiedPrerequisites,
                     defaults, USE_DEFAULTS, prover, relation_prover)
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

    def __init__(self, A, B, *, styles=None):
        '''
        Create the expression for (A subset_eq B)
        '''
        InclusionRelation.__init__(self, SubsetEq._operator_, A, B,
                                   styles=styles)

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

    def _readily_provable(self, *, check_transitive_pair=False):
        '''
        This SubsetEq relation is readily provable if the sets
        are provably equal or set equivalent, the corresponding
        Subset relation is provable, or
        '''
        from proveit.logic import Forall, Equals, InSet, SetEquiv
        if hasattr(self.superset, 'readily_includes'):
            # If the superset has a 'readily_includes' method, we may
            # use it as a faster way to check if this is readily 
            # provable.
            try:
                return self.superset.readily_includes(self.subset)
            except (NotImplementedError, UnsatisfiedPrerequisites):
                pass
        if Equals(self.subset, self.superset).readily_provable():
            return True
        if SetEquiv(self.subset, self.superset).proven():
            return True
        if InclusionRelation._readily_provable(
                self, check_transitive_pair=check_transitive_pair):
            return True

        # No worry about conflicts with assumptions because the 
        # variable will be bound by a quantifier:
        _x = safe_dummy_var(self, avoid_default_assumption_conflicts=False)
        # forall_{x in A} x in B => A subseteq B:
        univ_quant = Forall(_x, InSet(_x, self.superset), domain=self.subset)
        return univ_quant.proven()

    @prover
    def conclude(self, **defaults_config):
        from proveit import ProofFailure
        from proveit.logic import Equals, SetOfAll, SetEquiv
        from . import subset_eq_via_equality

        # Equal sets include each other.
        if Equals(*self.operands.entries).readily_provable() and (
                subset_eq_via_equality.is_usable()):
            return self.conclude_via_equality()

        # Equivalent sets include each other.
        # Using "proven" here on purpose.
        if SetEquiv(*self.operands.entries).proven():
            return self.conclude_via_equivalence()

        # Check for special case of basic set comprehension
        # [{x | Q(x)}_{x \in S}] \subseteq S
        if isinstance(self.subset, SetOfAll):
            
            from proveit import y, ExprTuple
            from proveit.logic import And
            from proveit.logic.sets.comprehension import (
                comprehension_is_subset)
            set_of_all = self.subset

            if (len(set_of_all.all_instance_vars()) == 1
                and (set_of_all.instance_element
                     == set_of_all.all_instance_vars()[0])
                and set_of_all.domain == self.superset):

                Q_op, Q_op_sub = (
                    Function(Q, set_of_all.all_instance_vars()),
                    And(*set_of_all.explicit_conditions()))
                _y_sub = set_of_all.all_instance_vars()[0]

                concluded = comprehension_is_subset.instantiate(
                    {S: set_of_all.domain, y:_y_sub, Q_op: Q_op_sub})

                return concluded

        _A, _B = self.operands.entries
        if hasattr(_A, 'deduce_superset_eq_relation'):
            return _A.deduce_superset_eq_relation(_B)
        if hasattr(_B, 'deduce_subset_eq_relation'):
            try:
                return _B.deduce_subset_eq_relation(_A)
            except (NotImplementedError, UnsatisfiedPrerequisites):
                pass

        try:
            # Attempt to conclude A subseteq B via
            # forall_{x in A} x in B.
            return self.conclude_as_folded()
        except ProofFailure as e:
            raise ProofFailure(self, defaults.assumptions,
                           "Failed to conclude as folded: %s.\n"
                           "To try to prove %s via transitive "
                           "relations, try 'conclude_via_transitivity'."
                           %(str(self), str(e)))

    @prover
    def conclude_via_equality(self, **defaults_config):
        from . import subset_eq_via_equality
        return subset_eq_via_equality.instantiate(
            {A: self.subset, B: self.superset})

    @prover
    def conclude_via_equivalence(self, **defaults_config):
        from . import subset_eq_via_equivalence
        return subset_eq_via_equivalence.instantiate(
            {A: self.subset, B: self.superset})

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Derive this folded version, A subseteq B, from the unfolded
        version, (forall_{x in A} x in B).
        '''
        from . import fold_subset_eq
        # No worry about conflicts with assumptions because the 
        # variable will be bound by a quantifier:
        _x = safe_dummy_var(self, avoid_default_assumption_conflicts=False)
        return fold_subset_eq.instantiate(
            {A: self.subset, B: self.superset, x: _x})
    
    @prover
    def unfold(self, elem_instance_var=None, **defaults_config):
        '''
        From A subset_eq B, derive and return (forall_{x in A} x in B).
        x will be relabeled if an elem_instance_var is supplied.
        '''
        from . import unfold_subset_eq
        if elem_instance_var is not None:
            temp_result = unfold_subset_eq.instantiate(
                {A: self.subset, B: self.superset})
            return temp_result.instantiate(
                {x: elem_instance_var}, num_forall_eliminations=0)
        return unfold_subset_eq.instantiate(
            {A: self.subset, B: self.superset})

    @prover
    def derive_superset_membership(self, element, **defaults_config):
        '''
        From A subset_eq B and element x in A, derive x in B.
        '''
        from . import unfold_subset_eq
        return unfold_subset_eq.instantiate(
            {A: self.subset, B: self.superset, x: element})

    @prover
    def derive_subset_nonmembership(self, element, **defaults_config):
        '''
        From A subset_eq B and element x not_in B, derive x not_in A.
        '''
        from . import refined_nonmembership
        return refined_nonmembership.instantiate(
            {A: self.subset, B: self.superset, x: element})
    
    @prover
    def apply_transitivity(self, other, **defaults_config):
        '''
        Apply a transitivity rule to derive from this A subseteq B
        expression and something of the form B subseteq C, B subset C,
        or B=C to obtain A subset C or A subseteq C as appropriate.
        '''
        from proveit.logic import Equals, SetEquiv, ProperSubset
        from . import (transitivity_subset_eq_subset,
                       transitivity_subset_subset_eq,
                       transitivity_subset_eq_subset_eq)
        other = as_expression(other)
        if isinstance(other, Equals) or isinstance(other, SetEquiv):
            return InclusionRelation.apply_transitivity(self, other)
        new_rel = None
        if other.subset == self.superset:
            if isinstance(other, ProperSubset):
                new_rel = transitivity_subset_eq_subset.instantiate(
                    {A: self.subset, B: self.superset, C: other.superset},
                    preserve_all=True)
            elif isinstance(other, SubsetEq):
                new_rel = transitivity_subset_eq_subset_eq.instantiate(
                    {A: self.subset, B: self.superset, C: other.superset},
                    preserve_all=True)
        elif other.superset == self.subset:
            if isinstance(other, ProperSubset):
                new_rel = transitivity_subset_subset_eq.instantiate(
                    {A: other.subset, B: other.superset, C: self.superset},
                    preserve_all=True)
            elif isinstance(other, SubsetEq):
                new_rel = transitivity_subset_eq_subset_eq.instantiate(
                    {A: other.subset, B: other.superset, C: self.superset},
                    preserve_all=True)
        if new_rel is None:
            raise ValueError(
                "Cannot perform transitivity with {0} and {1}!".
                format(self, other))
        return new_rel.with_mimicked_style(self)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce and return that this SubsetEq statement is
        in the Boolean set.
        '''
        from . import subset_eq_is_bool
        is_bool_stmt = subset_eq_is_bool.instantiate(
                {A: self.normal_lhs, B: self.normal_rhs})
        return is_bool_stmt.inner_expr().element.with_matching_style(self)

def superset_eq(A, B):
    '''
    Return the expression representing (A superset_eq B), internally
    represented as (B subset_eq A) but with a style that reverses
    the direction.
    '''
    return SubsetEq(B, A).with_styles(direction = 'reversed')
