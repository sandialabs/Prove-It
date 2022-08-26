from proveit import (Literal, Operation, USE_DEFAULTS, ProofFailure,
                     defaults, prover, relation_prover, equality_prover)
from proveit.logic.booleans.booleans import in_bool
from proveit import A, x, y, S


class Not(Operation):
    # operator of the Not operation
    _operator_ = Literal(
        string_format='not',
        latex_format=r'\lnot',
        theory=__file__)

    def __init__(self, A, *, styles=None):
        from proveit import ExprTuple
        Operation.__init__(self, Not._operator_, A, styles=styles)

    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically.
        '''
        from proveit.logic import FALSE, Equals
        #if self.operand != FALSE:  # avoid infinite recursion
        #    yield self.equate_negated_to_false  # A=FALSE given Not(A)
        #if not isinstance(self.operand, Equals):  # avoid infinite recursion
        #    yield self.derive_untrue  # A != TRUE given Not(A)
        if isinstance(self.operand, Not):
            yield self.derive_via_double_negation  # A given Not(Not(A))
        if self.operand.proven():
            # derive FALSE given Not(A) and A
            yield self.derive_contradiction
        yield self.derive_in_bool  # [Not(A) in Boolean] given Not(A)
        if hasattr(self.operand, 'negation_side_effects'):
            # derive negation side-effects for the specific type of
            # expression being negated.
            for neg_side_effect in self.operand.negation_side_effects(
                    judgment):
                yield neg_side_effect

    def in_bool_side_effects(self, judgment):
        '''
        From not(A) in Boolean deduce A in Boolean, where self is not(A).
        '''
        yield self.deduce_operand_in_bool

    def _readily_provable(self):
        '''
        Not(A) is readily provable if A is readily disprovable.
        '''
        # Note: here we need to call the '_' version; otherwise,
        # we will have an infinite recursion.
        return self.operand._readily_disprovable()

    def _readily_disprovable(self):
        '''
        Not(A) is readily provable if A is readily provable.
        '''
        return self.operand.readily_provable()

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to automatically conclude this negation via evaluation reductions
        or double negation.
        '''
        from proveit.logic import EvaluationError
        # as a last resort (conclude_negation on the operand should have been
        # tried first), conclude negation via evaluating the operand as false.
        try:
            self.operand.evaluation()
        except EvaluationError:
            raise ProofFailure(self, defaults.assumptions,
                               "Unable to evaluate %s" % str(self.operand))
        return self.conclude_via_falsified_negation()

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Try to conclude the negation of this negation via double negation.  That
        is, conclude not(not(A)), where self=not(A), via proving A.
        If that fails (e.g., an unusable theorem), call conclude on
        not(not(A)) directly.
        '''
        try:
            return Not(self).conclude_via_double_negation()
        except BaseException:
            return Not(self).conclude()

    def latex(self, fence=False, **kwargs):
        out_str = ''
        if fence:
            out_str += "("
        out_str += self.operator.latex() + ' ' + self.operand.latex(fence=True)
        if fence:
            out_str += ')'
        return out_str
    
    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        from proveit.logic import TRUE, FALSE, EvaluationError, evaluate_truth
        from proveit.logic.booleans.negation import (
                negation_intro, falsified_negation_intro)
        from . import not_t, not_f  # load in truth-table evaluations
        if self.operand == TRUE:
            return not_t
        elif self.operand == FALSE:
            return not_f
        elif self.operand.proven():
            # evaluate to FALSE via falsified_negation_intro
            return falsified_negation_intro.instantiate({A: self.operand})
        elif self.operand.disproven():
            # evaluate to TRUE via falsified_negation_intro
            return evaluate_truth(negation_intro.instantiate(
                    {A: self.operand}))
        elif must_evaluate:
            # The simplification of the operands may not have
            # worked hard enough.  Let's work harder if we must 
            # evaluate.
            evaluated = self.operand.evaluation().rhs
            if evaluated in (TRUE, FALSE):
                # All the pieces should be there now.
                return self.evaluation(automation=True)
            raise EvaluationError(self)
        
        if hasattr(self.operand, 'shallow_simplification_of_negation'):
            # If the operand has a 'shallow_simplification_of_negation',
            # use that.
            return self.operand.shallow_simplification_of_negation()
            
        # May now be able to evaluate via loaded truth tables.
        return Operation.shallow_simplification(self)

    @prover
    def substitute_in_false(self, lambda_map, **defaults_config):
        '''
        Given not(A), derive P(FALSE) from P(A).
        '''
        from proveit.logic.equality import substitute_in_false
        from proveit.logic import Equals
        from proveit import P
        Plambda = Equals._lambda_expr(lambda_map, self.operand)
        return substitute_in_false.instantiate(
            {x: self.operand, P: Plambda})

    @prover
    def substitute_falsehood(self, lambda_map, **defaults_config):
        '''
        Given not(A), derive P(A) from P(FALSE).
        '''
        from proveit.logic.equality import substitute_falsehood
        from proveit.logic import Equals
        from proveit.common import P
        Plambda = Equals._lambda_expr(lambda_map, self.operand)
        return substitute_falsehood.instantiate(
            {x: self.operand, P: Plambda})

    @relation_prover
    def derive_in_bool(self, **defaults_config):
        '''
        From Not(A) derive [Not(A) in Boolean].
        '''
        from proveit.logic.booleans import in_bool_if_true
        return in_bool_if_true.instantiate({A: self})

    def readily_in_bool(self):
        '''
        Returns True if we can readily prove that the operand is
        provably boolean and therefore this negation is boolean.
        '''
        from . import closure
        if not closure.is_usable():
            return False
        return in_bool(self.operand).readily_provable()

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Attempt to deduce, then return, that this 'not' expression is 
        in the set of BOOLEANS.
        '''
        from . import closure, double_neg_closure
        if isinstance(self.operand, Not):
            return double_neg_closure.instantiate(
                    {A: self.operand.operand})
        return closure.instantiate({A: self.operand})

    @prover
    def deduce_operand_in_bool(self, **defaults_config):
        '''
        Attempt to deduce, then return, that the negated operand is in 
        the set of BOOLEANS.
        '''
        from . import operand_is_bool
        return operand_is_bool.instantiate({A: self.operand})

    @prover
    def equate_negated_to_false(self, **defaults_config):
        r'''
        From not(A), derive and return A = FALSE.
        Note, see Equals.derive_via_boolean_equality for the reverse 
        process.
        '''
        from . import negation_elim
        return negation_elim.instantiate({A: self.operand})

    @prover
    def derive_untrue(self, **defaults_config):
        r'''
        From not(A), derive and return A != TRUE.
        '''
        from . import untrue_from_negation
        return untrue_from_negation.instantiate({A: self.operand})

    @prover
    def double_negation_equivalence(self, **defaults_config):
        r'''
        Given not(not(A)), deduce and return not(not(A)) = A.
        '''
        from . import double_negation_equiv
        if isinstance(self.operand, Not):
            return double_negation_equiv.instantiate(
                {A: self.operand.operand})
        raise ValueError(
            "double_negation_equivalence does not apply to " +
            str(self) +
            " which is not of the form not(not(A))")

    @prover
    def derive_via_double_negation(self, **defaults_config):
        r'''
        From not(not(A)), derive and return A.
        Note, see Equals.derive_via_boolean_equality for the reverse process.
        '''
        from . import double_negation_elim
        if isinstance(self.operand, Not):
            return double_negation_elim.instantiate(
                {A: self.operand.operand})
        raise ValueError(
            "derive_via_double_negation does not apply to " +
            str(self) +
            " which is not of the form not(not(A))")

    @prover
    def conclude_via_double_negation(self, **defaults_config):
        r'''
        Prove and return self of the form not(not(A)) assuming A.
        Also see version in NotEquals for A != FALSE.
        '''
        from . import double_negation_intro
        if isinstance(self.operand, Not):
            stmt = self.operand.operand
            return double_negation_intro.instantiate({A: stmt})

    @prover
    def conclude_via_falsified_negation(self, **defaults_config):
        r'''
        Prove and return self of the form not(A) assuming A=FALSE.
        '''
        from . import negation_intro
        return negation_intro.instantiate({A: self.operand})

    @prover
    def derive_contradiction(self, **defaults_config):
        r'''
        From not(A), and assuming A, derive and return FALSE.
        '''
        from . import negation_contradiction
        return negation_contradiction.instantiate({A: self.operand})

    @prover
    def affirm_via_contradiction(self, conclusion, **defaults_config):
        '''
        From not(A), derive the conclusion provided that the negated 
        conclusion implies both not(A) as well as A, and the conclusion 
        is a Boolean.
        '''
        from proveit.logic.booleans.implication import affirm_via_contradiction
        return affirm_via_contradiction(self, conclusion)

    @prover
    def deny_via_contradiction(self, conclusion, **defaults_config):
        '''
        From not(A), derive the negated conclusion provided that the 
        conclusion implies both not(A) as well as A, and the conclusion 
        is a Boolean.
        '''
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self, conclusion)

    @prover
    def deduce_double_negation_equiv(self, **defaults_config):
        '''
        For some not(not(A)), derive and return A = not(not(A)) 
        assuming A in Boolean.
        '''
        from . import double_negation_equiv
        if isinstance(self.operand, Not):
            Asub = self.operand.operand
            return double_negation_equiv.instantiate({A: Asub})
