from proveit import Literal, Operation, defaults, USE_DEFAULTS, composite_expression, ProofFailure
from proveit.logic.booleans.negation import Not
from proveit import A, B, C
from proveit import TransitiveRelation


class Implies(TransitiveRelation):
    _operator_ = Literal(
        string_format='=>',
        latex_format=r'\Rightarrow',
        theory=__file__)

    # map left-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, antecedent, consequent):
        TransitiveRelation.__init__(
            self, Implies._operator_, antecedent, consequent)
        self.antecedent = antecedent
        self.consequent = consequent

    @staticmethod
    def WeakRelationClass():
        '''
        The Strong and Weak form of transitive relations are the same for implication.
        It counts as a weak form because (A => A) is always true.
        '''
        return Implies

    @staticmethod
    def StrongRelationClass():
        '''
        The Strong and Weak form of transitive relations are the same for implication.
        '''
        return Implies

    def side_effects(self, judgment):
        '''
        Yield the TransitiveRelation side-effects (which also records
        known_left_sides nd known_right_sides).  Also derive the consequent
        as a side-effect if the antecedent is known to be true
        (under the "side-effect" assumptions).
        As a special case, if the consequent is FALSE, do
        derive_via_contradiction.
        '''
        from proveit.logic.booleans import FALSE
        for side_effect in TransitiveRelation.side_effects(self, judgment):
            yield side_effect
        if self.antecedent.proven():
            yield self.derive_consequent  # B given A=>B and A
        if self.consequent == FALSE:
            # Not(A) given A=>FALSE or A given Not(A)=>FALSE
            yield self.derive_via_contradiction

    def negation_side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically when an implication is negated.
        implemented by JML on 6/17/19
        '''
        yield self.deduce_negated_left_impl  # Not(A <=> B) given Not(B => A)
        yield self.deduce_negated_right_impl  # Not(A <=> B) given Not(A => B)
        yield self.deduce_negated_reflex  # B => A given Not(A => B)

    def conclude(self, assumptions):
        '''
        Try to automatically conclude this implication by reducing its
        operands to true/false, or by doing a "transitivity" search
        amongst known true implications whose assumptions are covered by
        the given assumptions.
        '''
        from . import (
            true_implies_true, false_implies_true, false_implies_false,
            false_antecedent_implication, falsified_antecedent_implication,
            untrue_antecedent_implication)
        from proveit.logic import TRUE, FALSE, NotEquals, EvaluationError
        if self.antecedent == self.consequent:
            return self.conclude_self_implication()

        if self in {
                true_implies_true,
                false_implies_true,
                false_implies_false}:
            # should be proven via one of the imported theorems as a simple
            # special case
            try:
                return self.evaluation(assumptions)
            except BaseException:
                return self.prove()

        if self.antecedent == FALSE:
            # The antecedent is FALSE, so we should try to prove the
            # implication via false_antecedent_implication.
            return false_antecedent_implication.instantiate(
                {A: self.consequent}, assumptions=assumptions)
        elif NotEquals(self.antecedent, TRUE).proven(assumptions):
            # The antecedent is known to be not equal to true, so
            # prove the implication via untrue_antecedent_implication.
            return untrue_antecedent_implication.instantiate(
                {A: self.antecedent, B: self.consequent},
                assumptions=assumptions)
        elif (self.antecedent.disproven(assumptions) or
              self.consequent.disproven(assumptions)):
            # Either the consequent or the antecedent has been disproven
            # so we should try to prove the implication via
            # falsified_antecedent_implication.
            return falsified_antecedent_implication.instantiate(
                {A: self.antecedent, B: self.consequent},
                assumptions=assumptions)
        elif self.consequent.proven(assumptions):
            # The consequent is proven, so we can prove the implication
            # via Deduction.
            return self.consequent.prove(assumptions).as_implication(
                self.antecedent)

        try:
            antecedent_eval = self.antecedent.evaluated(assumptions)
            if antecedent_eval == FALSE:
                # try again with the antecedent disproven
                return self.conclude(assumptions)
        except (EvaluationError, ProofFailure):
            pass

        try:
            consequent_eval = self.consequent.evaluated(assumptions)
            if consequent_eval in (FALSE, TRUE):
                # try again with the consequent proven or disproven.
                return self.conclude(assumptions)
        except (EvaluationError, ProofFailure):
            pass

        try:
            # try to prove the implication via deduction.
            return self.consequent.prove(
                tuple(assumptions) + (self.antecedent,)).as_implication(self.antecedent)
        except ProofFailure:
            raise ProofFailure(self, assumptions,
                               "Unable to automatically conclude by "
                               "standard means.  To try to prove this via "
                               "transitive implication relations, try "
                               "'conclude_via_transitivity'.")

    def conclude_negation(self, assumptions=USE_DEFAULTS):
        '''
        Try to conclude True when Not(TRUE => FALSE) is called.
        implemented by JML on 6/18/19
        '''
        from proveit.logic.booleans import FALSE, TRUE
        try:
            if self.antecedent == TRUE and self.consequent == FALSE:
                from . import true_implies_false_negated
        except BaseException:
            pass

    def conclude_via_double_negation(self, assumptions=USE_DEFAULTS):
        '''
        From A => B return A => Not(Not(B)).
        implemented by JML on 6/18/19
        '''
        from . import double_negate_consequent
        if isinstance(self.consequent.operand, Not):
            return double_negate_consequent.instantiate(
                {A: self.antecedent, B: self.consequent.operand.operand}, assumptions=assumptions)
        return "Not of the form 'A => B'"

    def derive_consequent(self, assumptions=USE_DEFAULTS):
        r'''
        From A => B derive and return B assuming A.
        '''
        from proveit._core_.proof import ModusPonens
        self.antecedent.prove(assumptions)
        return ModusPonens(self, assumptions).proven_truth

    def derive_iff(self, assumptions=USE_DEFAULTS):
        r'''
        From A => B derive and return A <=> B assuming B => A.
        '''
        from proveit.logic import Iff
        return Iff(self.A, self.B).conclude_via_definition()

    def deduce_negated_right_impl(self, assumptions=USE_DEFAULTS):
        r'''
        From Not(A => B) derive and return Not(A <=> B).
        implemented by JML on 6/18/19
        '''
        from . import not_iff_via_not_right_impl
        return not_iff_via_not_right_impl.instantiate(
            {A: self.antecedent, B: self.consequent}, assumptions=assumptions)

    def deduce_negated_left_impl(self, assumptions=USE_DEFAULTS):
        r'''
        From Not(B => A) derive and return Not(A <=> B).
        implemented by JML on 6/18/19
        '''
        from . import not_iff_via_not_left_impl
        return not_iff_via_not_left_impl.instantiate(
            {B: self.antecedent, A: self.consequent}, assumptions=assumptions)

    def deduce_negated_reflex(self, assumptions=USE_DEFAULTS):
        # implemented by JML on 6/18/19
        from . import negated_reflex
        return negated_reflex.instantiate(
            {A: self.antecedent, B: self.consequent}, assumptions=assumptions)

    def deny_antecedent(self, assumptions=USE_DEFAULTS):
        '''
        From A => B, derive and return Not(A) assuming Not(B).
        '''
        from . import modus_tollens_affirmation, modus_tollens_denial
        if isinstance(self.antecedent, Not):
            return modus_tollens_affirmation.instantiate(
                {A: self.antecedent.operand, B: self.consequent}, assumptions=assumptions)
        else:
            return modus_tollens_denial.instantiate(
                {A: self.antecedent, B: self.consequent}, assumptions=assumptions)

    def apply_transitivity(self, other_impl, assumptions=USE_DEFAULTS):
        '''
        From :math:`A \Rightarrow B` (self) and a given :math:`B \Rightarrow C` (other_impl), derive and return :math:`A \Rightarrow C`.
        '''
        from . import implication_transitivity
        if self.consequent == other_impl.antecedent:
            return implication_transitivity.instantiate(
                {A: self.antecedent, B: self.consequent, C: other_impl.consequent}, assumptions=assumptions)
        elif self.antecedent == other_impl.consequent:
            return implication_transitivity.instantiate(
                {A: other_impl.antecedent, B: self.antecedent, C: self.consequent}, assumptions=assumptions)

    def derive_via_contradiction(self, assumptions=USE_DEFAULTS):
        r'''
        From (Not(A) => FALSE), derive and return A assuming A in Boolean.
        Or from (A => FALSE), derive and return Not(A) assuming A in Boolean.
        Or from (A => FALSE), derive and return A != TRUE.
        '''
        from proveit.logic import FALSE, in_bool
        from . import affirmation_via_contradiction, denial_via_contradiction
        from . import not_true_via_contradiction
        if self.consequent != FALSE:
            raise ValueError(
                'derive_via_contradiction method is only applicable if FALSE is implicated, not for ' +
                str(self))
        if isinstance(self.antecedent, Not):
            stmt = self.antecedent.operand
            return affirmation_via_contradiction.instantiate(
                {A: stmt}, assumptions=assumptions)
        else:
            if in_bool(self.antecedent).proven(assumptions):
                return denial_via_contradiction.instantiate(
                    {A: self.antecedent}, assumptions=assumptions)
            else:
                return not_true_via_contradiction.instantiate(
                    {A: self.antecedent}, assumptions=assumptions)

    def conclude_self_implication(self):
        from . import self_implication
        if self.antecedent != self.consequent:
            raise ValueError(
                'May only conclude a self implementation when the antecedent and consequent are the same')
        return self_implication.instantiate({A: self.antecedent})

    def generalize(self, forall_vars, domain=None, conditions=tuple()):
        r'''
        This makes a generalization of this expression, prepending Forall
        operations according to new_forall_vars and new_conditions and/or new_domain
        that will bind 'arbitrary' free variables.  This overrides the expr
        version to absorb antecedent into conditions if they match.  For example,
        :math:`[A(x) \Rightarrow [B(x, y) \Rightarrow P(x, y)]]` generalized
        forall :math:`x, y` such that :math:`A(x), B(x, y)`
        becomes :math:`\forall_{x, y | A(x), B(x, y)} P(x, y)`,
        '''
        from proveit.logic import InSet
        hypothesized_conditions = set()
        conditions_set = set(composite_expression(conditions))
        if domain is not None:
            # add in the effective conditions from the domain
            for var in composite_expression(forall_vars):
                conditions_set.add(InSet(var, domain))
        expr = self
        while isinstance(expr, Implies) and expr.antecedent in conditions_set:
            hypothesized_conditions.add(expr.antecedent)
            expr = expr.consequent
        if len(hypothesized_conditions) == 0:
            # Just use the expr version
            return expr.generalize(self, forall_vars, domain, conditions)
        return expr.generalize(expr, forall_vars, domain, conditions)
        # return Forall(new_forall_vars, expr, new_conditions)

    def contrapose(self, assumptions=USE_DEFAULTS):
        '''
        Depending upon the form of self with respect to negation of the antecedent and/or consequent,
        will derive from self and return as follows:

        * From :math:`[\lnot A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[\lnot A \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow \lnot B]`, derive :math:`[B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`.
        * From :math:`[A  \Rightarrow B]`, derive :math:`[\lnot B \Rightarrow \lnot A]` assuming :math:`A \in \mathcal{B}`, :math:`B \in \mathcal{B}`.
        '''
        from . import from_contraposition, to_contraposition, contrapose_neg_consequent, contrapose_neg_antecedent
        from proveit.logic import Not
        if isinstance(
                self.antecedent,
                Not) and isinstance(
                self.consequent,
                Not):
            return from_contraposition.instantiate(
                {B: self.antecedent.operand, A: self.consequent.operand}, assumptions=assumptions)
        elif isinstance(self.antecedent, Not):
            return contrapose_neg_antecedent.instantiate(
                {A: self.antecedent.operand, B: self.consequent}, assumptions=assumptions)
        elif isinstance(self.consequent, Not):
            return contrapose_neg_consequent.instantiate(
                {A: self.antecedent, B: self.consequent.operand}, assumptions=assumptions)
        else:
            return to_contraposition.instantiate(
                {A: self.antecedent, B: self.consequent}, assumptions=assumptions)

    def evaluation(self, assumptions=USE_DEFAULTS, automation=True):
        '''
        Given operands that evaluate to TRUE or FALSE, derive and
        return the equality of this expression with TRUE or FALSE.
        '''
        # load in truth-table evaluations
        from . import implies_t_f
        from . import implies_t_t, implies_f_t, implies_f_f
        return Operation.evaluation(self, assumptions, automation=automation)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this implication expression is in the set of BOOLEANS.
        '''
        from . import implication_closure
        return implication_closure.instantiate(
            {A: self.antecedent, B: self.consequent}, assumptions=assumptions)


def conclude_via_implication(consequent, assumptions):
    '''
    Perform a breadth-first search of implications going in reverse from the consequent
    until reaching an antecedent that has been proven.
    '''
    visited = set()
    # map antecedents to consequents that arise durent the breadth-first search
    consequent_map = dict()
    queue = [consequent]
    while len(queue) > 0:
        expr = queue.pop()
        if expr not in visited:
            visited.add(expr)
            if expr not in Implies.known_right_sides:
                continue  # no known implications with the expr as the consequent; skip it
            for known_implication in Implies.known_right_sides[expr]:
                # see if the known_implication is applicable under the given
                # set of assumptions
                if known_implication.is_sufficient(assumptions):
                    local_antecedent, local_consequent = known_implication.antecedent, known_implication.consequent
                    consequent_map[local_antecedent] = local_consequent
                    try:
                        known_implication.antecedent.prove(
                            assumptions, automation=False)
                        # found a solution; use it by deriving "local"
                        # consequents until getting to the desired consequent
                        while True:
                            judgment = Implies(
                                local_antecedent,
                                local_consequent).derive_consequent(
                                assumptions=assumptions)
                            if judgment.expr == consequent:
                                return judgment
                            local_antecedent = judgment.expr
                            local_consequent = consequent_map[local_antecedent]
                    except ProofFailure:
                        queue.append(local_antecedent)
    raise ProofFailure(
        consequent,
        assumptions,
        'Unable to conclude via implications')


def affirm_via_contradiction(contradictory_expr, conclusion, assumptions):
    '''
    Affirms the conclusion via reductio ad absurdum.
    First calls derive_contradiction on the contradictory_expr to derive FALSE,
    then derive the conclusion after proving that the negated conclusion
    implies FALSE.  The conclusion must be a Boolean.
    '''
    from proveit.logic import Not
    assumptions = defaults.checked_assumptions(assumptions)
    extended_assumptions = assumptions + (Not(conclusion),)
    return contradictory_expr.derive_contradiction(extended_assumptions).as_implication(
        Not(conclusion)).derive_via_contradiction(assumptions)


def deny_via_contradiction(contradictory_expr, conclusion, assumptions):
    '''
    Deny the conclusion (affirm its negation) via reductio ad absurdum.
    First calls derive_contradiction on the contradictory_expr to derive FALSE,
    then derive the negated conclusion after proving that the conclusion itself
    implies FALSE.  The conclusion must be a Boolean.
    '''
    from proveit.logic import Not
    assumptions = defaults.checked_assumptions(assumptions)
    extended_assumptions = assumptions + (conclusion,)
    return contradictory_expr.derive_contradiction(extended_assumptions).as_implication(
        conclusion).derive_via_contradiction(assumptions)
