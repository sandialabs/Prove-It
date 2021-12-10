from proveit import (Literal, Operation, USE_DEFAULTS, ProofFailure,
                     UnsatisfiedPrerequisites, prover, equality_prover)
from .equals import Equals
from proveit.logic.irreducible_value import is_irreducible_value
from proveit import x, y, A, X
from proveit.relation import Relation


class NotEquals(Relation):
    # operator of the NotEquals operation
    _operator_ = Literal(
        string_format='!=',
        latex_format=r'\neq',
        theory=__file__)

    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, NotEquals._operator_, (a, b),
                           styles=styles)
        self.lhs = self.operands[0]
        self.rhs = self.operands[1]

    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for
        this NotEquals operation.
        '''
        from proveit.logic.booleans import FALSE
        # automatically derive the reversed form which is equivalent
        yield self.derive_reversed  # y != x from x != y
        if self.rhs == FALSE:
            yield self.derive_via_double_negation  # A from A != False and A in Boolean
        yield self.unfold  # Not(x=y) from x != y

    @prover
    def conclude(self, **defaults_config):
        from proveit.logic import SimplificationError, FALSE, Not
        if is_irreducible_value(self.lhs) and is_irreducible_value(self.rhs):
            # prove that two irreducible values are not equal
            return self.lhs.not_equal(self.rhs)
        if self.lhs == FALSE or self.rhs == FALSE:
            try:
                # prove something is not false by proving it to be true
                return self.conclude_via_double_negation()
            except BaseException:
                pass
        if Not(Equals(self.lhs, self.rhs)).proven():
            # Conclude (x ≠ y) by knowing that Not(x = y) is true. 
            return self.conclude_as_folded()
        # See if either side has a simplification.
        simplifications = []
        for operand in self.operands:
            try:
                simplification = operand.simplification()
                if simplification.rhs == operand:
                    simplification = None # reflection doesn't count
            except (SimplificationError, ProofFailure):
                pass
            simplifications.append(simplification)
        lhs_simp = simplifications[0]
        rhs_simp = simplifications[1]
        if lhs_simp is not None and rhs_simp is not None:
            # There are known simplifications of lhs and rhs.
            # Use them.
            neq = NotEquals(lhs_simp.rhs, rhs_simp.rhs).prove()
            neq = neq.inner_expr().lhs.substitute(self.lhs)
            neq = neq.inner_expr().rhs.substitute(self.rhs)
            return neq
        elif lhs_simp is not None:
            # The left side has a known simplification; use it.
            neq = NotEquals(lhs_simp.rhs, self.rhs).prove()
            return neq.inner_expr().lhs.substitute(self.lhs)
        elif rhs_simp is not None:
            # The right side has a known simplification; use it.
            neq = NotEquals(self.lhs, rhs_simp.rhs).prove()
            return neq.inner_expr().rhs.substitute(self.rhs)
        if hasattr(self.lhs, 'not_equal'):
            # If there is a 'not_equal' method, use that.
            # The responsibility then shifts to that method for
            # determining what strategies should be attempted
            # (with the recommendation that it should not attempt
            # multiple non-trivial automation strategies).
            # A good practice is to try the 'conclude_as_folded'
            # strategy if it doesn't fall into any specially-handled
            # case.
            return self.lhs.not_equal(self.rhs)
        return self.conclude_as_folded()

    @prover
    def derive_reversed(self, **defaults_config):
        '''
        From x != y derive y != x.
        '''
        from . import not_equals_symmetry
        return not_equals_symmetry.instantiate({x: self.lhs, y: self.rhs})

    def reversed(self):
        '''
        Return an NotEquals expression with the right side and left side
        reversed from this one. This is not a derivation: see derive_reversed().
        '''
        return NotEquals(self.rhs, self.lhs)

    @prover
    def derive_via_double_negation(self, **defaults_config):
        '''
        From A != FALSE, derive and return A assuming in_bool(A).
        Also see version in Not class.
        '''
        from proveit.logic import FALSE
        from proveit.logic.booleans import from_not_false
        if self.rhs == FALSE:
            return from_not_false.instantiate({A: self.lhs})
        raise ValueError(
            "derive_via_double_negation does not apply to " +
            str(self) +
            " which is not of the form A != FALSE")

    @prover
    def conclude_via_double_negation(self, **defaults_config):
        '''
        Prove and return self of the form A != FALSE or FALSE != A assuming A.
        Also see version in Not class.
        '''
        from proveit.logic import FALSE
        from proveit.logic.booleans import not_equals_false
        if self.lhs == FALSE:
            # switch left and right sides and prove it that way.
            NotEquals(self.rhs, self.lhs).prove()
            return self.prove()
        if self.rhs == FALSE:
            return not_equals_false.instantiate({A: self.lhs})

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Return (x != y) = Not(x=y) where self represents (x != y).
        '''
        from . import not_equals_def
        return not_equals_def.instantiate({x: self.lhs, y: self.rhs})

    @prover
    def unfold(self, **defaults_config):
        '''
        From (x != y), derive and return Not(x=y).
        '''
        from . import unfold_not_equals
        # Don't auto-simplify.  If (x=y) has a known evaluation,
        # unfolding to obtain prove TRUE or FALSE would never
        # be a desired behavior -- for FALSE, call derive_contradiction
        # instead.
        return unfold_not_equals.instantiate({x: self.lhs, y: self.rhs},
                                             auto_simplify=False)

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Conclude (x != y) from Not(x = y).
        '''
        from . import fold_not_equals
        return fold_not_equals.instantiate(
            {x: self.lhs, y: self.rhs})

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        If the left side has a 'not_equal' method, use that for
        evalaution.  Otherwise, if appropriate (must_evaluate is TRUE
        or the answer is already known) apply the definition to
        perform the evaluation: A ≠ B via ￢(A = B).
        '''
        from proveit import ProofFailure
        from proveit.logic import evaluate_truth
        if self.lhs != self.rhs and hasattr(self.lhs, 'not_equal'):
            try:
                # If there is a 'not_equal' method, try to use that.
                neq = self.lhs.not_equal(self.rhs, automation=must_evaluate)
                return evaluate_truth(neq)
            except ProofFailure:
                pass
        eq = Equals(self.lhs, self.rhs)
        if must_evaluate or eq.proven() or eq.disproven():
            # Evaluate A ≠ B via evaluating ￢(A = B), 
            definition_equality = self.definition()
            unfolded_evaluation = definition_equality.rhs.evaluation(
                    automation=must_evaluate)
            return definition_equality.apply_transitivity(unfolded_evaluation)
        return Operation.shallow_simplification(self)

    @prover
    def derive_contradiction(self, **defaults_config):
        r'''
        From x != y, and assuming x = y, derive and return FALSE.
        '''
        from . import not_equals_contradiction
        return not_equals_contradiction.instantiate(
            {x: self.lhs, y: self.rhs})

    @prover
    def affirm_via_contradiction(self, conclusion, **defaults_config):
        '''
        From x != y, derive the conclusion provided that the negated
        conclusion implies x != y and x = y, and the conclusion is a 
        Boolean.
        '''
        from proveit.logic.booleans.implication import affirm_via_contradiction
        return affirm_via_contradiction(self, conclusion)

    @prover
    def deny_via_contradiction(self, conclusion, **defaults_config):
        '''
        From x != y, derive the negated conclusion provided that the 
        conclusion implies x != y and x = y, and the conclusion is a 
        Boolean.
        '''
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self, conclusion)

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce and return that this 'not equals' statement is in the 
        set of BOOLEANS.
        '''
        from . import not_equals_is_bool
        return not_equals_is_bool.instantiate({x: self.lhs, y: self.rhs})
