from proveit import (as_expression, defaults, USE_DEFAULTS, 
                     ProofFailure, prover)
from proveit import Literal
from proveit import TransitiveRelation, TransitivityException
from proveit.logic.irreducible_value import (
        IrreducibleValue, is_irreducible_value)
from proveit import A, B, C, P, f, x, y, z


class SetEquiv(TransitiveRelation):
    '''
    Class to capture the membership equivalence of 2 sets A and B.
    SetEquiv(A, B) is a claim that all elements of A are also elements
    of B and vice-versa. The SetEquiv relation uses the congruence
    symbol to distinguish the SetEquiv claim from the stronger claim
    that A = B.
    '''
    # operator for the SetEquiv relation
    _operator_ = Literal(string_format='equiv', latex_format=r'\cong',
                         theory=__file__)

    # map Expressions to sets of Judgments of set equivalences that
    # involve the Expression on the left hand or right hand side.
    # known_equalities = dict()
    known_equivalences = dict()

    # Map Expressions to a subset of known_equivalences that are
    # deemed to effect simplifications of the inner expression
    # on the right hand side according to some canonical method
    # of simplication determined by each operation.
    simplifications = dict()

    # Specific simplifications that simplify the inner expression to
    # IrreducibleValue objects.
    evaluations = dict()

    # Record found inversions.  See the invert method.
    # Maps (lambda_map, rhs) pairs to a list of
    # (known_equivalence, inversion) pairs, recording previous results
    # of the invert method for future reference.
    inversions = dict()

    # Record the SetEquiv objects being initialized (to avoid infinite
    # recursion while automatically deducing an equality is in the
    # Boolean set).
    initializing = set()

    def __init__(self, a, b, *, styles=None):
        TransitiveRelation.__init__(self, SetEquiv._operator_, a, b, 
                                    styles=styles)
        if self not in SetEquiv.initializing:
            SetEquiv.initializing.add(self)
            try:
                # proactively prove (a equiv b) in Boolean.
                self.deduce_in_bool()
            except BaseException:
                # may fail before the relevent _axioms_ have
                # been generated
                pass  # and that's okay
            SetEquiv.initializing.remove(self)

    def side_effects(self, judgment):
        '''
        Record the judgment in SetEquiv.known_equivalences, associated
        from the left hand side and the right hand side.  This
        information may be useful for concluding new equivalences via
        transitivity. If the right hand side is an "irreducible value"
        (see is_irreducible_value), also record it in
        SetEquiv.evaluations for use when the evaluation method is
        called. Some side-effects derivations are also attempted
        depending upon the form of this equivalence.
        '''
        from proveit.logic.booleans import TRUE, FALSE
        SetEquiv.known_equivalences.setdefault(self.lhs, set()).add(judgment)
        SetEquiv.known_equivalences.setdefault(self.rhs, set()).add(judgment)
        # not yet clear if the irreducible value check is relevant for sets
        # if is_irreducible_value(self.rhs):
        #     SetEquiv.simplifications.setdefault(self.lhs, set()).add(judgment)
        #     SetEquiv.evaluations.setdefault(self.lhs, set()).add(judgment)
        if (self.lhs != self.rhs):  # e.g. if we don't have SetEquiv(A, A)
            # automatically derive the reversed form which is equivalent
            yield self.derive_reversed
        
        # STILL CHECKING ON THE RELEVANCE OF THE FOLLOWING
        # if hasattr(self.lhs, 'equality_side_effects'):
        #     for side_effect in self.lhs.equality_side_effects(judgment):
        #         yield side_effect

    def negation_side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for a
        negated equivalence. IN PROGRESS
        '''
        from proveit.logic.booleans import FALSE
        yield self.deduce_not_equiv  # A not_equiv B from not(A equiv B)

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude the equivalence in various ways:
        simple reflexivity (A equiv A), via an evaluation (if one side
        is an irreducible), or via transitivity.
        IN PROGRESS
        '''
        if self.lhs == self.rhs:
            try:
                # Trivial A = A
                return self.conclude_via_reflexivity()
            except BaseException:
                pass  # e.g., reflexivity theorem may not be usable
        try:
            return self.conclude_as_folded()
        except ProofFailure:
            raise ProofFailure(self, defaults.assumptions,
                               "Unable to automatically conclude by "
                               "standard means.  To try to prove this via "
                               "transitive implication relations, try "
                               "'conclude_via_transitivity'.")

    #     if self.lhs or self.rhs in (TRUE, FALSE):
    #         try:
    #             # Try to conclude as TRUE or FALSE.
    #             return self.conclude_boolean_equality(assumptions)
    #         except ProofFailure:
    #             pass
    #     if is_irreducible_value(self.rhs):
    #         try:
    #             evaluation = self.lhs.evaluation(assumptions)
    #             if evaluation.rhs != self.rhs:
    #                 raise ProofFailure(self, assumptions, "Does not match with evaluation: %s"%str(evaluation))
    #             return evaluation
    #         except SimplificationError as e:
    #             raise ProofFailure(self, assumptions, "Evaluation error: %s"%e.message)
    #     elif is_irreducible_value(self.lhs):
    #         try:
    #             evaluation = self.rhs.evaluation(assumptions)
    #             if evaluation.rhs != self.lhs:
    #                 raise ProofFailure(self, assumptions, "Does not match with evaluation: %s"%str(evaluation))
    #             return evaluation.derive_reversed()
    #         except SimplificationError as e:
    #             raise ProofFailure(self, assumptions, "Evaluation error: %s"%e.message)
    #     try:
    #         Implies(self.lhs, self.rhs).prove(assumptions, automation=False)
    #         Implies(self.rhs, self.lhs).prove(assumptions, automation=False)
    #         # lhs => rhs and rhs => lhs, so attempt to prove lhs = rhs via lhs <=> rhs
    #         # which works when they can both be proven to be Boolean.
    #         try:
    #             return Iff(self.lhs, self.rhs).derive_equality(assumptions)
    #         except:
    #             from proveit.logic.booleans.implication import eq_from_mutual_impl
    #             return eq_from_mutual_impl.instantiate({A:self.lhs, B:self.rhs}, assumptions=assumptions)
    #     except ProofFailure:
    #         pass

    #     """
    #     # Use conclude_equality if available
    #     if hasattr(self.lhs, 'conclude_equality'):
    #         return self.lhs.conclude_equality(assumptions)
    #     if hasattr(self.rhs, 'conclude_equality'):
    #         return self.rhs.conclude_equality(assumptions)
    #     """
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        return TransitiveRelation.conclude(self)

    # @staticmethod
    # def known_relations_from_left(expr, assumptions_set):
    #     '''
    #     For each Judgment that is an Equals involving the given expression on
    #     the left hand side, yield the Judgment and the right hand side.
    #     '''
    #     for judgment in Equals.known_equalities.get(expr, frozenset()):
    #         if judgment.lhs == expr:
    #             if judgment.is_applicable(assumptions_set):
    #                 yield (judgment, judgment.rhs)

    # @staticmethod
    # def known_relations_from_right(expr, assumptions_set):
    #     '''
    #     For each Judgment that is an Equals involving the given expression on
    #     the right hand side, yield the Judgment and the left hand side.
    #     '''
    #     for judgment in Equals.known_equalities.get(expr, frozenset()):
    #         if judgment.rhs == expr:
    #             if judgment.is_applicable(assumptions_set):
    #                 yield (judgment, judgment.lhs)

    @prover
    def conclude_via_reflexivity(self, **defaults_config):
        '''
        Prove and return self of the form A equiv A.
        '''
        from . import set_equiv_reflexivity
        assert self.lhs == self.rhs, (
                "self.lhs ({0}) is not set-equiv to self.rhs ({1})".
                format(self.lhs, self.rhs))
        return set_equiv_reflexivity.instantiate({A: self.lhs})

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        From forall_{x} (x in A) = (x in B),
        conclude A set_equiv B.
        '''
        from . import set_equiv_fold
        return set_equiv_fold.instantiate({A: self.lhs, B: self.rhs})

    @prover
    def unfold(self, **defaults_config):
        '''
        From A set_equiv B derive forall_{x} [(x in A) = (x in B)].
        A set_equiv B must be known, provable, or assumed to be True.
        For example,
            SetEquiv(Set(1, 2, 3), Set(a, b, c)).unfold(
                assumptions=[SetEquiv(Set(1, 2, 3), Set(a, b, c))])
        returns:
            SetEquiv({1, 2, 3}, {a, b, c}) |-
            forall_{x} [(x in {1, 2, 3}) = (x in {a, b, c})]
        '''
        from . import set_equiv_unfold
        return set_equiv_unfold.instantiate({A: self.lhs, B: self.rhs})

    @prover
    def derive_reversed(self, **defaults_config):
        '''
        From A set_equiv B derive B set_equiv A.
        This derivation is an automatic side-effect.
        '''
        from . import set_equiv_reversal
        return set_equiv_reversal.instantiate({A: self.lhs, B: self.rhs})

    @prover
    def deduce_not_equiv(self, **defaults_config):
        '''
        Deduce A not_equiv B assuming not(A equiv B),
        where self is (A equiv B).
        '''
        from .set_not_equiv import SetNotEquiv
        return SetNotEquiv(self.lhs, self.rhs).conclude_as_folded()

    @prover
    def apply_transitivity(self, other, **defaults_config):
        '''
        From A set_equiv B (self) and B set_equiv C (other) derive and
        return A set_equiv C.
        If "other" is not a SetEquiv, reverse roles and call
        'apply_transitivity' from the "other" side.
        This method initially based on the apply_transitivity method
        from Equals class.
        '''
        from . import set_equiv_transitivity
        other = as_expression(other)
        if not isinstance(other, SetEquiv):
            # If the other relation is not "SetEquiv",
            # call from the "other" side.
            return other.apply_transitivity(self)
        other_set_equiv = other
        # We can assume that B set_equiv A will be a Judgment if
        # A set_equiv B is a Judgment because it is derived as a
        # side-effect.
        if self.rhs == other_set_equiv.lhs:
            return set_equiv_transitivity.instantiate(
                {A: self.lhs, B: self.rhs, C: other_set_equiv.rhs})
        elif self.rhs == other_set_equiv.rhs:
            return set_equiv_transitivity.instantiate(
                {A: self.lhs, B: self.rhs, C: other_set_equiv.lhs})
        elif self.lhs == other_set_equiv.lhs:
            return set_equiv_transitivity.instantiate(
                {A: self.rhs, B: self.lhs, C: other_set_equiv.rhs})
        elif self.lhs == other_set_equiv.rhs:
            return set_equiv_transitivity.instantiate(
                {A: self.rhs, B: self.lhs, C: other_set_equiv.lhs})
        else:
            raise TransitivityException(
                self, defaults.assumptions,
                'Transitivity cannot be applied unless there is '
                'something in common in the set equivalences: '
                '%s vs %s' % (str(self), str(other)))

    def sub_left_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From A equiv B, and given P(B), derive P(A) assuming P(B).
        UNDER CONSTRUCTION, adapted from Equals class.
        P(x) is provided via lambda_map as a Lambda expression or
        an object that returns a Lambda expression when calling
        lambda_map() (see proveit.lambda_map,
        proveit.lambda_map.SubExprRepl in particular), or, if neither
        of those, an expression upon which to perform a global
        replacement of self.rhs.
        '''
        from . import sub_left_side_into
        from proveit.logic import Equals
        Plambda = Equals._lambda_expr(lambda_map, self.rhs)

        return sub_left_side_into.instantiate(
            {A: self.lhs, B: self.rhs, P: Plambda}, assumptions=assumptions)

    def sub_right_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From A equiv B, and given P(A), derive P(B) assuming P(A).
        UNDER CONSTRUCTION, adapted from Equals class.
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling
        lambda_map() (see proveit.lambda_map,
        proveit.lambda_map.SubExprRepl in particular), or, if neither
        of those, an expression upon which to perform a global
        replacement of self.lhs.
        '''
        from . import sub_right_side_into
        from proveit.logic import Equals
        Plambda = Equals._lambda_expr(lambda_map, self.lhs)
        return sub_right_side_into.instantiate(
            {A: self.lhs, B: self.rhs, P: Plambda}, assumptions=assumptions)

    @prover
    def deduce_in_bool(self,  **defaults_config):
        '''
        Deduce and return that this SetEquiv claim is in the Boolean
        set.
        '''
        from . import set_equiv_is_bool
        return set_equiv_is_bool.instantiate({A: self.lhs, B: self.rhs})
