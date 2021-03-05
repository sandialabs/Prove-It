from proveit import as_expression, defaults, USE_DEFAULTS, ProofFailure
from proveit import Literal, Operation, Lambda, ArgumentExtractionError
from proveit import TransitiveRelation, TransitivityException
from proveit.logic.irreducible_value import is_irreducible_value
from proveit import A, B, P, Q, f, n, x, y, z


class Equals(TransitiveRelation):
    # operator of the Equals operation
    _operator_ = Literal(string_format='=', theory=__file__)

    # Map Expressions to sets of Judgments of equalities that involve
    # the Expression on the left hand or right hand side.
    known_equalities = dict()

    # Map each Expression/Assumptions combination to a single
    # known_equality deemed to effect a simplification of the inner
    # expression on the rhs according to some canonical method of
    # simplification determined by each operation. For example, the
    # Expression expr = Floor(Add(x, two)) under the assumption that x
    # is a Real, would have dictionary key (expr, (InSet(x, Real))) with
    # an eventual value of something like |- expr = Floor(x) + two.
    known_simplifications = dict()

    # Specific simplifications that simplify the inner expression to
    # IrreducibleValue objects.
    known_evaluation_sets = dict()

    # Record found inversions.  See the invert method.
    # Maps (lambda_map, rhs) pairs to a list of
    # (known_equality, inversion) pairs, recording previous results
    # of the invert method for future reference.
    inversions = dict()

    # Record the Equals objects being initialized (to avoid infinite
    # recursion while automatically deducing an equality is in Boolean).
    initializing = set()

    def __init__(self, a, b):
        TransitiveRelation.__init__(self, Equals._operator_, a, b)
        '''
        # May be better not to be proactive but we need to see if this
        # breaks anything.
        if self not in Equals.initializing:
            Equals.initializing.add(self)
            try:
                self.deduce_in_bool() # proactively prove (a=b) in Boolean.
            except:
                # may fail before the relevent _axioms_ have been generated
                pass # and that's okay
            Equals.initializing.remove(self)
        '''

    def side_effects(self, judgment):
        '''
        Record the judgment in Equals.known_equalities, associated from
        the left hand side and the right hand side.  This information
        may be useful for concluding new equations via transitivity.
        If the right hand side is an "irreducible value" (see
        is_irreducible_value), also record it in
        Equals.known_evaluation_sets for use when the evaluation
        method is called.   Some side-effects derivations are also
        attempted depending upon the form of this equality.
        If the rhs is an "irreducible value" (see is_irreducible_value),
        also record the judgment in the Equals.known_simplifications
        and Equals.known_evaluation_sets dictionaries, for use when the
        simplification or evaluation method is called. The key for the
        known_simplifications dictionary is the specific *combination*
        of the lhs expression along with the assumptions in the form
        (expr, tuple(sorted(assumptions))); the key for the
        known_evaluation_sets dictionary is just the lhs expression
        without the specific assumptions. Some side-effects
        derivations are also attempted depending upon the form of this
        equality.
        '''
        from proveit.logic.booleans import TRUE, FALSE
        Equals.known_equalities.setdefault(self.lhs, set()).add(judgment)
        Equals.known_equalities.setdefault(self.rhs, set()).add(judgment)

        if is_irreducible_value(self.rhs):
            assumptions_sorted = sorted(judgment.assumptions,
                                        key=lambda expr: hash(expr))
            lhs_key = (self.lhs, tuple(assumptions_sorted))
            # n.b.: the values in the known_simplifications
            # dictionary consist of single Judgments not sets
            Equals.known_simplifications[lhs_key] = judgment
            Equals.known_evaluation_sets.setdefault(
                self.lhs, set()).add(judgment)

        if (self.lhs != self.rhs):
            # automatically derive the reversed form which is equivalent
            yield self.derive_reversed
        if self.rhs == FALSE:
            try:
                self.lhs.prove(automation=False)
                # derive FALSE given lhs=FALSE and lhs.
                yield self.derive_contradiction
            except ProofFailure:
                pass
            # Use this form after merging in 'Expression.proven' commite:
            # if self.lhs.proven(): # If lhs is proven using default assumptions.
            #    # derive FALSE given lhs=FALSE and lhs.
            #    yield self.derive_contradiction
        if self.rhs in (TRUE, FALSE):
            # automatically derive A from A=TRUE or Not(A) from A=FALSE
            yield self.derive_via_boolean_equality
        if hasattr(self.lhs, 'equality_side_effects'):
            for side_effect in self.lhs.equality_side_effects(judgment):
                yield side_effect

    def negation_side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for a negated
        equation.
        '''
        yield self.deduce_not_equals  # A != B from not(A=B)

    def conclude(self, assumptions):
        '''
        Attempt to conclude the equality various ways:
        simple reflexivity (x=x), via an evaluation (if one side is an
        irreducible). Use conclude_via_transitivity for transitivity cases.
        '''
        from proveit.logic import TRUE, FALSE, Implies, Iff, in_bool
        if self.lhs == self.rhs:
            # Trivial x=x
            return self.conclude_via_reflexivity()
        if (self.lhs in (TRUE, FALSE)) or (self.rhs in (TRUE, FALSE)):
            try:
                # Try to conclude as TRUE or FALSE.
                return self.conclude_boolean_equality(assumptions)
            except ProofFailure:
                pass
        if is_irreducible_value(self.rhs):
            try:
                evaluation = self.lhs.evaluation(assumptions)
                if evaluation.rhs != self.rhs:
                    raise ProofFailure(
                        self,
                        assumptions,
                        "Does not match with evaluation: %s" %
                        str(evaluation))
                return evaluation
            except EvaluationError as e:
                raise ProofFailure(self, assumptions,
                                   "Evaluation error: %s" % e.message)
        elif is_irreducible_value(self.lhs):
            try:
                evaluation = self.rhs.evaluation(assumptions)
                if evaluation.rhs != self.lhs:
                    raise ProofFailure(
                        self,
                        assumptions,
                        "Does not match with evaluation: %s" %
                        str(evaluation))
                return evaluation.derive_reversed()
            except EvaluationError as e:
                raise ProofFailure(self, assumptions,
                                   "Evaluation error: %s" % e.message)

        if (Implies(self.lhs, self.rhs).proven(assumptions) and
                Implies(self.rhs, self.lhs).proven(assumptions) and
                in_bool(self.lhs).proven(assumptions) and
                in_bool(self.rhs).proven(assumptions)):
            # There is mutual implication both sides are known to be
            # boolean.  Conclude equality via mutual implication.
            return Iff(self.lhs, self.rhs).derive_equality(assumptions)
        
        # check the equivalence set.

        if hasattr(self.lhs, 'deduce_equality'):
            # If there is a 'deduce_equality' method, use that.
            # The responsibility then shifts to that method for
            # determining what strategies should be attempted
            # (with the recommendation that it should not attempt
            # multiple non-trivial automation strategies).
            eq = self.lhs.deduce_equality(self, assumptions)
            if eq.expr != self:
                raise ValueError("'deduce_equality' not implemented "
                                 "correctly; must deduce the 'equality' "
                                 "that it is given if it can: "
                                 "'%s' != '%s'" % (eq.expr, self))
            return eq
        else:
            '''
            If there is no 'deduce_equality' method, we'll try
            simplifying each side to see if they are equal.
            '''
            # Try to prove equality via simplifying both sides.
            lhs_simplification = self.lhs.simplification(assumptions)
            rhs_simplification = self.rhs.simplification(assumptions)
            simplified_lhs = lhs_simplification.rhs
            simplified_rhs = rhs_simplification.rhs
            try:
                if simplified_lhs != self.lhs or simplified_rhs != self.rhs:
                    simplified_eq = Equals(
                        simplified_lhs, simplified_rhs).prove(assumptions)
                    return Equals.apply_transitivities(
                        [lhs_simplification, simplified_eq, rhs_simplification],
                        assumptions)
            except ProofFailure:
                pass
        raise ProofFailure(self, assumptions,
                           "Unable to automatically conclude by "
                           "standard means.  To try to prove this via "
                           "transitive relations, try "
                           "'conclude_via_transitivity'.")

    @staticmethod
    def WeakRelationClass():
        return Equals  # = is the strong and weak form of equality,

    @staticmethod
    def StrongRelationClass():
        return Equals  # = is the strong and weak form of equality,

    def known_relations_from_left(expr, assumptions_set):
        '''
        For each Judgment that is an Equals involving the given expression on
        the left hand side, yield the Judgment and the right hand side.
        '''
        for judgment in Equals.known_equalities.get(expr, frozenset()):
            if judgment.lhs == expr:
                if judgment.is_sufficient(assumptions_set):
                    yield (judgment, judgment.rhs)

    @staticmethod
    def known_relations_from_right(expr, assumptions_set):
        '''
        For each Judgment that is an Equals involving the given expression on
        the right hand side, yield the Judgment and the left hand side.
        '''
        for judgment in Equals.known_equalities.get(expr, frozenset()):
            if judgment.rhs == expr:
                if judgment.is_sufficient(assumptions_set):
                    yield (judgment, judgment.lhs)

    def conclude_via_reflexivity(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form x = x.
        '''
        from . import equals_reflexivity
        assert self.lhs == self.rhs
        return equals_reflexivity.instantiate({x: self.lhs})

    def derive_reversed(self, assumptions=USE_DEFAULTS):
        '''
        From x = y derive y = x.  This derivation is an automatic side-effect.
        '''
        from . import equals_reversal
        return equals_reversal.instantiate(
            {x: self.lhs, y: self.rhs}, assumptions=assumptions)

    def reversed(self):
        '''
        Return an Equals expression with the right side and left side reversed
        from this one.  This is not a derivation: see derive_reversed().
        '''
        return Equals(self.rhs, self.lhs)

    @staticmethod
    def yield_known_equal_expressions(expr, assumptions=USE_DEFAULTS):
        '''
        Yield everything known to be equal to the given expression
        under the given assumptions directly or indirectly through 
        the transitive property of equality.
        '''
        assumptions = defaults.checked_assumptions(assumptions)
        to_process = {expr}
        processed = set()
        while len(to_process) > 0:
            expr = to_process.pop()
            yield expr
            processed.add(expr)
            if expr not in Equals.known_equalities:
                continue
            for known_equality in Equals.known_equalities[expr]:
                if known_equality.is_sufficient(assumptions):
                    # A valid equality.  See if something is new.
                    for operand in known_equality.operands:
                        if operand not in processed:
                            to_process.add(operand)

    def deduce_not_equals(self, assumptions=USE_DEFAULTS):
        r'''
        Deduce x != y assuming not(x = y), where self is x=y.
        '''
        from .not_equals import NotEquals
        return NotEquals(self.lhs, self.rhs).conclude_as_folded(assumptions)

    def deduce_negated(self, i, assumptions=USE_DEFAULTS):
        from proveit.logic.booleans.conjunction import falsified_and_if_not_right, falsified_and_if_not_left, falsified_and_if_neither
        if i == 0:
            # Deduce Not(A and B) from Not(A).
            return falsified_and_if_not_right.instantiate(
                {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        if i == 1:
            return falsified_and_if_not_left.instantiate(
                {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        else:
            return falsified_and_if_neither.instantiate(
                {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def apply_transitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        From x = y (self) and y = z (other) derive and return x = z.
        Also works more generally as long as there is a common side to the equations.
        If "other" is not an equality, reverse roles and call 'apply_transitivity'
        from the "other" side.
        '''
        from . import equals_transitivity
        other = as_expression(other)
        if not isinstance(other, Equals):
            # If the other relation is not "Equals", call from the "other"
            # side.
            return other.apply_transitivity(self, assumptions)
        other_equality = other
        # We can assume that y=x will be a Judgment if x=y is a Judgment
        # because it is derived as a side-effect.
        if self.rhs == other_equality.lhs:
            return equals_transitivity.instantiate(
                {x: self.lhs, y: self.rhs, z: other_equality.rhs}, assumptions=assumptions)
        elif self.rhs == other_equality.rhs:
            return equals_transitivity.instantiate(
                {x: self.lhs, y: self.rhs, z: other_equality.lhs}, assumptions=assumptions)
        elif self.lhs == other_equality.lhs:
            return equals_transitivity.instantiate(
                {x: self.rhs, y: self.lhs, z: other_equality.rhs}, assumptions=assumptions)
        elif self.lhs == other_equality.rhs:
            return equals_transitivity.instantiate(
                {x: self.rhs, y: self.lhs, z: other_equality.lhs}, assumptions=assumptions)
        else:
            raise TransitivityException(
                self,
                assumptions,
                'Transitivity cannot be applied unless there is something in common in the equalities: %s vs %s' %
                (str(self),
                 str(other)))

    def derive_via_boolean_equality(self, assumptions=USE_DEFAULTS):
        '''
        From A = TRUE derive A, or from A = FALSE derive Not(A).  This derivation
        is an automatic side-effect.
        Note, see derive_stmt_eq_true or Not.equate_negated_to_false for the reverse process.
        '''
        from proveit.logic import TRUE, FALSE
        from proveit.logic.booleans import eq_true_elim
        from proveit.logic import Not
        if self.rhs == TRUE:
            return eq_true_elim.instantiate(
                {A: self.lhs}, assumptions=assumptions)  # A
        elif self.rhs == FALSE:
            return Not(
                self.lhs).conclude_via_falsified_negation(
                assumptions=assumptions)  # Not(A)

    def derive_contradiction(self, assumptions=USE_DEFAULTS):
        '''
        From A=FALSE, and assuming A, derive FALSE.
        '''
        from proveit.logic import FALSE
        from . import contradiction_via_falsification
        if self.rhs == FALSE:
            return contradiction_via_falsification.instantiate(
                {A: self.lhs}, assumptions=assumptions)
        raise ValueError(
            'Equals.derive_contradiction is only applicable if the right-hand-side is FALSE')

    def affirm_via_contradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From (A=FALSE), derive the conclusion provided that the negated conclusion
        implies both (A=FALSE) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.booleans.implication import affirm_via_contradiction
        return affirm_via_contradiction(self, conclusion, assumptions)

    def deny_via_contradiction(self, conclusion, assumptions=USE_DEFAULTS):
        '''
        From (A=FALSE), derive the negated conclusion provided that the conclusion
        implies both (A=FALSE) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self, conclusion, assumptions)

    def conclude_boolean_equality(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return self of the form (A=TRUE) assuming A, A=FALSE assuming Not(A), [Not(A)=FALSE] assuming A.
        '''
        from proveit.logic import TRUE, FALSE, Not
        from proveit.logic.booleans import eq_true_intro
        if self.rhs == TRUE:
            return eq_true_intro.instantiate(
                {A: self.lhs}, assumptions=assumptions)
        elif self.rhs == FALSE:
            if isinstance(self.lhs, Not):
                evaluation = self.lhs.evaluation(assumptions=assumptions)
                if evaluation.rhs == self.rhs:
                    return evaluation
            else:
                return Not(self.lhs).equate_negated_to_false(assumptions)
        elif self.lhs == TRUE or self.lhs == FALSE:
            return Equals(self.rhs, self.lhs).conclude_boolean_equality(
                assumptions).derive_reversed(assumptions)
        raise ProofFailure(
            self,
            assumptions,
            "May only conclude via boolean equality if one side of the equality is TRUE or FALSE")

    def derive_is_in_singleton(self, assumptions=USE_DEFAULTS):
        '''
        From (x = y), derive (x in {y}).
        '''
        from proveit.logic.sets.enumeration import fold_singleton
        return fold_singleton.instantiate(
            {x: self.lhs, y: self.rhs}, assumptions=assumptions)

    @staticmethod
    def _lambda_expr(
            lambda_map,
            expr_being_replaced,
            assumptions=USE_DEFAULTS):
        from proveit import ExprRange, InnerExpr
        if isinstance(lambda_map, InnerExpr):
            lambda_map = lambda_map.repl_lambda()
        if not isinstance(lambda_map, Lambda):
            # as a default, do a global replacement
            lambda_map = Lambda.global_repl(lambda_map, expr_being_replaced)
        if lambda_map.parameters.num_entries() != 1:
            raise ValueError("When substituting, expecting a single "
                             "'lambda_map' parameter entry which may "
                             "be a single parameter or a range; got "
                             "%s as 'lambda_map'" % lambda_map)
        if isinstance(lambda_map.parameters[0], ExprRange):
            from proveit.numbers import one
            if lambda_map.parameters[0].start_index != one:
                raise ValueError("When substituting a range, expecting "
                                 "the 'lambda_map' parameter range to "
                                 "have a starting index of 1; got "
                                 "%s as 'lambda_map'" % lambda_map)
        return lambda_map

    def substitution(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given f(x), derive f(x)=f(y).
        f(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from proveit import ExprRange, Conditional
        from . import substitution

        if isinstance(lambda_map, Conditional):
            conditional = lambda_map
            if self.lhs == conditional.value:
                # Return the substitution equality for swapping out
                # the value of a conditional which may implicitly
                # assume that the condition is satisfied.
                return conditional.value_substitution(self, assumptions)

        lambda_map = Equals._lambda_expr(lambda_map, self.lhs, assumptions)
        
        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use operands_substitution for ExprTuple
            # substitution.
            from proveit.core_expr_types.operations import \
                operands_substitution
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return operands_substitution.instantiate(
                {n: n_sub, f: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)
        # Regular single-operand substitution:
        return substitution.instantiate(
            {f: lambda_map, x: self.lhs, y: self.rhs}, assumptions=assumptions)

    def sub_left_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(y), derive P(x) assuming P(y).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.rhs.
        '''
        from proveit import ExprRange
        from . import sub_left_side_into
        from . import substitute_truth, substitute_in_true, substitute_falsehood, substitute_in_false
        from proveit.logic import TRUE, FALSE
        lambda_map = Equals._lambda_expr(lambda_map, self.rhs)

        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use sub_in_left_operands for ExprTuple
            # substitution.
            from proveit.logic.equality import \
                sub_in_left_operands
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return sub_in_left_operands.instantiate(
                {n: n_sub, P: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)

        try:
            # try some alternative proofs that may be shorter, if they
            # are usable
            if self.rhs == TRUE:
                # substitute_truth may provide a shorter proof option
                substitute_truth.instantiate({x: self.lhs, P: lambda_map},
                                             assumptions=assumptions)
            elif self.lhs == TRUE:
                # substitute_in_true may provide a shorter proof option
                substitute_in_true.instantiate({x: self.rhs, P: lambda_map},
                                               assumptions=assumptions)
            elif self.rhs == FALSE:
                # substitute_falsehood may provide a shorter proof option
                substitute_falsehood.instantiate({x: self.lhs, P: lambda_map},
                                                 assumptions=assumptions)
            elif self.lhs == FALSE:
                # substitute_in_false may provide a shorter proof option
                substitute_in_false.instantiate({x: self.rhs, P: lambda_map},
                                                assumptions=assumptions)
        except BaseException:
            pass
        return sub_left_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map},
            assumptions=assumptions)

    def sub_right_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x = y, and given P(x), derive P(y) assuming P(x).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from proveit import ExprRange
        from . import sub_right_side_into
        from . import substitute_truth, substitute_in_true, substitute_falsehood, substitute_in_false
        from proveit.logic import TRUE, FALSE
        lambda_map = Equals._lambda_expr(lambda_map, self.lhs)

        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use sub_in_right_operands for ExprTuple
            # substitution.
            from proveit.logic.equality import \
                sub_in_right_operands
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return sub_in_right_operands.instantiate(
                {n: n_sub, P: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)

        try:
            # try some alternative proofs that may be shorter, if they are
            # usable
            if self.lhs == TRUE:
                # substitute_truth may provide a shorter proof options
                substitute_truth.instantiate({x: self.rhs, P: lambda_map},
                                             assumptions=assumptions)
            elif self.rhs == TRUE:
                # substitute_in_true may provide a shorter proof options
                substitute_in_true.instantiate({x: self.lhs, P: lambda_map},
                                               assumptions=assumptions)
            elif self.lhs == FALSE:
                # substitute_falsehood may provide a shorter proof options
                substitute_falsehood.instantiate({x: self.rhs, P: lambda_map},
                                                 assumptions=assumptions)
            elif self.rhs == FALSE:
                # substitute_in_false may provide a shorter proof options
                substitute_in_false.instantiate({x: self.lhs, P: lambda_map},
                                                assumptions=assumptions)
        except BaseException:
            pass
        return sub_right_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map},
            assumptions=assumptions)

    def derive_right_via_equality(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive B (the Right-Hand-Side) assuming A.
        '''
        from . import rhs_via_equality
        return rhs_via_equality.instantiate(
            {P: self.lhs, Q: self.rhs}, assumptions=assumptions)

    def derive_left_via_equality(self, assumptions=USE_DEFAULTS):
        '''
        From A = B, derive A (the Right-Hand-Side) assuming B.
        '''
        from . import lhs_via_equality
        return lhs_via_equality.instantiate(
            {P: self.lhs, Q: self.rhs}, assumptions=assumptions)

    def other_side(self, expr):
        '''
        Returns the 'other' side of the of the equation if the given expr is on one side.
        '''
        if expr == self.lhs:
            return self.rhs
        elif expr == self.rhs:
            return self.lhs
        raise ValueError(
            'The given expression is expected to be one of the sides of the equation')

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce and return that this equality statement is in the Boolean set.
        '''
        from . import equality_in_bool
        return equality_in_bool.instantiate({x: self.lhs, y: self.rhs})

    def evaluation(self, assumptions=USE_DEFAULTS, automation=True):
        '''
        Given operands that may be evaluated to irreducible values that
        may be compared, or if there is a known evaluation of this
        equality, derive and return this expression equated to
        TRUE or FALSE.
        '''
        if automation:
            if self.lhs == self.rhs:
                # prove equality is true by reflexivity
                return evaluate_truth(self.prove().expr, assumptions=[])
            if is_irreducible_value(
                    self.lhs) and is_irreducible_value(
                    self.rhs):
                # Irreducible values must know how to evaluate the equality
                # between each other, where appropriate.
                return self.lhs.eval_equality(self.rhs)
            return TransitiveRelation.evaluation(self, assumptions)
        return Operation.evaluation(self, assumptions, automation)

    @staticmethod
    def invert(lambda_map, rhs, assumptions=USE_DEFAULTS):
        '''
        Given some x -> f(x) map and a right-hand-side, find the
        x for which f(x) = rhs amongst known equalities under the
        given assumptions.  Return this x if one is found; return
        None otherwise.
        '''
        assumptions_set = set(defaults.checked_assumptions(assumptions))
        if (lambda_map, rhs) in Equals.inversions:
            # Previous solution(s) exist.  Use one if the assumptions are
            # sufficient.
            for known_equality, inversion in Equals.inversions[(
                    lambda_map, rhs)]:
                if known_equality.is_sufficient(assumptions_set):
                    return inversion
        # The mapping may be a trivial identity: f(x) = f(x)
        try:
            x = lambda_map.extract_argument(rhs)
            # Found a trivial inversion.  Store it for future reference.
            known_equality = Equals(rhs, rhs).prove()
            Equals.inversions.setdefault(
                (lambda_map, rhs), []).append(
                (known_equality, x))
            return x  # Return the found inversion.
        except ArgumentExtractionError:
            pass  # well, it was worth a try
        # Search among known relations for a solution.
        for known_equality, lhs in Equals.known_relations_from_right(
                rhs, assumptions_set):
            try:
                x = lambda_map.extract_argument(lhs)
                # Found an inversion.  Store it for future reference.
                Equals.inversions.setdefault(
                    (lambda_map, rhs), []).append(
                    (known_equality, x))
                return x  # Return the found inversion.
            except ArgumentExtractionError:
                pass  # not a match.  keep looking.
        raise InversionError(
            "No inversion found to map %s onto %s" %
            (str(lambda_map), str(rhs)))


def reduce_operands(
        inner_expr,
        in_place=True,
        must_evaluate=False,
        assumptions=USE_DEFAULTS):
    '''
    Attempt to return an InnerExpr object that is provably equivalent to
    the given inner_expr but with simplified operands at the
    inner-expression level.
    If in_place is True, the top-level expression must be a Judgment
    and the simplified Judgment is derived instead of an equivalence
    relation.
    If must_evaluate is True, the simplified
    operands must be irreducible values (see is_irreducible_value).
    '''
    # Any of the operands that can be simplified must be replaced with
    # their simplification.
    from proveit import InnerExpr, ExprRange
    assert isinstance(inner_expr, InnerExpr), \
        "Expecting 'inner_expr' to be of type 'InnerExpr'"
    inner = inner_expr.expr_hierarchy[-1]
    substitutions = []
    while True:
        all_reduced = True
        for operand in inner.operands:
            if (not is_irreducible_value(operand) and
                    not isinstance(operand, ExprRange)):
                # The operand isn't already irreducible, so try to
                # simplify it.
                if must_evaluate:
                    operand_eval = operand.evaluation(assumptions=assumptions)
                else:
                    operand_eval = operand.simplification(
                        assumptions=assumptions)
                if must_evaluate and not is_irreducible_value(
                        operand_eval.rhs):
                    msg = 'Evaluations expected to be irreducible values'
                    raise EvaluationError(msg, assumptions)
                if operand_eval.lhs != operand_eval.rhs:
                    # Compose map to replace all instances of the
                    # operand within the inner expression.
                    global_repl = Lambda.global_repl(inner, operand)
                    lambda_map = inner_expr.repl_lambda().compose(global_repl)
                    # substitute in the evaluated value
                    if in_place:
                        subbed = operand_eval.sub_right_side_into(lambda_map)
                        inner_expr = InnerExpr(
                            subbed, inner_expr.inner_expr_path)
                    else:
                        sub = operand_eval.substitution(lambda_map)
                        inner_expr = InnerExpr(
                            sub.rhs, inner_expr.inner_expr_path)
                        substitutions.append(sub)
                    all_reduced = False
                    # Start over since there may have been multiple
                    # substitutions:
                    break
        if all_reduced:
            break  # done!
        inner = inner_expr.expr_hierarchy[-1]

    if not in_place and len(substitutions) > 1:
        # When there have been multiple substitutions, apply
        # transtivity over the chain of substitutions to equate the
        # end-points.
        Equals.apply_transitivities(substitutions, assumptions)
    return inner_expr


"""
def conclude_via_reduction(expr, assumptions):
    '''
    Attempts to prove that the given expression is TRUE under the
    given assumptions via evaluating that the expression is equal to true.
    Returns the resulting Judgment if successful.
    '''
    from proveit.lambda_map import SubExprRepl
    if not isinstance(expr, Operation):
        # Can only really do reduction on an Operation.  But we can
        # try to do a proof by evaluation.
        expr.evaluation(assumptions)
        return expr.prove(assumptions)
    # reduce the operands
    reduced_expr = reduce_operands(expr, assumptions)
    # prove the reduced version
    judgment = reduced_expr.prove(assumptions)
    # now rebuild the original via sub_left_side_into (for a shorter proof than substitutions)
    for k, operand in enumerate(expr.operands):
        # for each operand, replace it with the original
        sub_expr_repl = SubExprRepl(judgment).operands[k]
        judgment = operand.evaluation(assumptions=assumptions).sub_left_side_into(sub_expr_repl, assumptions)
    assert judgment.expr == expr, 'Equivalence substitutions did not work out as they should have'
    return judgment
"""


def default_simplification(inner_expr, in_place=False, must_evaluate=False,
                           operands_only=False, assumptions=USE_DEFAULTS,
                           automation=True):
    '''
    Default attempt to simplify the given inner expression under the
    given assumptions.  If successful, returns a Judgment (using a
    subset of the given assumptions) that expresses an equality between
    the expression (on the left) and one with a simplified form for the
    "inner" part (in some canonical sense determined by the Operation).
    If in_place is True, the top-level expression must be a Judgment
    and the simplified Judgment is derived instead of an equivalence
    relation.
    If must_evaluate=True, the simplified form must be an irreducible
    value (see is_irreducible_value).  Specifically, this method checks to
    see if an appropriate simplification/evaluation has already been
    proven.  If not, but if it is an Operation, call the
    simplification/evaluation method on all operands, make these
    substitions, then call simplification/evaluation on the expression
    with operands substituted for simplified forms.  It also treats,
    as a special case, evaluating the expression to be true if it is in
    the set of assumptions [also see Judgment.evaluation and
    evaluate_truth].  If operands_only = True, only simplify the operands
    of the inner expression.
    '''
    # among other things, convert any assumptions=None
    # to assumptions=() to avoid len(None) errors
    assumptions = defaults.checked_assumptions(assumptions)

    from proveit.logic import TRUE, FALSE
    from proveit.logic.booleans import true_axiom
    top_level = inner_expr.expr_hierarchy[0]
    inner = inner_expr.expr_hierarchy[-1]
    if operands_only:
        # Just do the reduction of the operands at the level below the
        # "inner expression"
        reduced_inner_expr = reduce_operands(
            inner_expr, in_place, must_evaluate, assumptions)
        if in_place:
            try:
                return reduced_inner_expr.expr_hierarchy[0].prove(
                    assumptions, automation=False)
            except BaseException:
                assert False
        try:
            eq = Equals(top_level, reduced_inner_expr.expr_hierarchy[0])
            return eq.prove(assumptions, automation=False)
        except BaseException:
            assert False

    def inner_simplification(inner_equivalence):
        if in_place:
            return inner_equivalence.sub_right_side_into(
                inner_expr, assumptions=assumptions)
        return inner_equivalence.substitution(inner_expr,
                                              assumptions=assumptions)
    if is_irreducible_value(inner):
        return Equals(inner, inner).prove()
    assumptions_set = set(defaults.checked_assumptions(assumptions))

    # See if the expression is already known to be true as a special
    # case.
    try:
        inner.prove(assumptions_set, automation=False)
        true_eval = evaluate_truth(inner, assumptions_set)  # A=TRUE given A
        if inner == top_level:
            if in_place:
                return true_axiom
            else:
                return true_eval
        return inner_simplification(true_eval)
    except BaseException:
        pass
    # See if the negation of the expression is already known to be true
    # as a special case.
    try:
        inner.disprove(assumptions_set, automation=False)
        false_eval = evaluate_falsehood(
            inner, assumptions_set)  # A=FALSE given Not(A)
        return inner_simplification(false_eval)
    except BaseException:
        pass

    # ================================================================ #
    # See if the expression already has a proven simplification        #
    # ================================================================ #

    # construct the key for the known_simplifications dictionary
    assumptions_sorted = sorted(assumptions, key=lambda expr: hash(expr))
    known_simplifications_key = (inner, tuple(assumptions_sorted))

    if (must_evaluate and inner in Equals.known_evaluation_sets):
        evaluations = Equals.known_evaluation_sets[inner]
        candidates = []
        for judgment in evaluations:
            if judgment.is_sufficient(assumptions_set):
                # Found existing evaluation suitable for the assumptions
                candidates.append(judgment)
        if len(candidates) >= 1:
            # Return the "best" candidate with respect to fewest number
            # of steps.
            def min_key(judgment): return judgment.proof().num_steps()
            simplification = min(candidates, key=min_key)
            return inner_simplification(simplification)

    elif (not must_evaluate and
          known_simplifications_key in Equals.known_simplifications):
        simplification = Equals.known_simplifications[known_simplifications_key]
        if simplification.is_usable():
            return inner_simplification(simplification)

    # ================================================================ #

    if not automation:
        msg = 'Unknown evaluation (without automation): ' + str(inner)
        raise SimplificationError(msg)

    # See if the expression is equal to something that has an evaluation
    # or is already known to be true.
    if inner in Equals.known_equalities:
        for known_eq in Equals.known_equalities[inner]:
            try:
                if known_eq.is_sufficient(assumptions_set):
                    if in_place:
                        # Should first substitute in the known
                        # equivalence then simplify that.
                        if inner == known_eq.lhs:
                            known_eq.sub_right_side_into(
                                inner_expr, assumptions)
                        elif inner == known_eq.rhs:
                            known_eq.sub_left_side_into(
                                inner_expr, assumptions)
                    # Use must_evaluate=True.  Simply being equal to
                    # something simplified isn't necessarily the
                    # appropriate simplification for "inner" itself.
                    alt_inner = known_eq.other_side(inner).inner_expr()
                    equiv_simp = \
                        default_simplification(alt_inner, in_place=in_place,
                                               must_evaluate=True,
                                               assumptions=assumptions,
                                               automation=False)
                    if in_place:
                        # Returns Judgment with simplification:
                        return equiv_simp
                    inner_equiv = known_eq.apply_transitivity(equiv_simp,
                                                              assumptions)
                    if inner == top_level:
                        return inner_equiv
                    return inner_equiv.substitution(inner_expr,
                                                    assumptions=assumptions)
            except SimplificationError:
                pass
    # try to simplify via reduction
    if not isinstance(inner, Operation):
        if must_evaluate:
            raise EvaluationError('Unknown evaluation: ' + str(inner),
                                  assumptions)
        else:
            # don't know how to simplify, so keep it the same
            return inner_simplification(Equals(inner, inner).prove())
    reduced_inner_expr = reduce_operands(inner_expr, in_place, must_evaluate,
                                         assumptions)
    if reduced_inner_expr == inner_expr:
        if must_evaluate:
            # Since it wasn't irreducible to begin with, it must change
            # in order to evaluate.
            raise SimplificationError('Unable to evaluate: ' + str(inner))
        else:
            raise SimplificationError('Unable to simplify: ' + str(inner))
    # evaluate/simplify the reduced inner expression
    inner = reduced_inner_expr.expr_hierarchy[-1]
    if must_evaluate:
        inner_equiv = inner.evaluation(assumptions)
    else:
        inner_equiv = inner.simplification(assumptions)
    value = inner_equiv.rhs
    if value == TRUE:
        # Attempt to evaluate via proving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluate_truth(inner, assumptions)
        except BaseException:
            pass
    if value == FALSE:
        # Attempt to evaluate via disproving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluate_falsehood(inner, assumptions)
        except BaseException:
            pass
    reduced_simplification = inner_simplification(inner_equiv)
    if in_place:
        simplification = reduced_simplification
    else:
        # Via transitivity, go from the original expression to the
        # reduced expression (simplified inner operands) and then the
        # final simplification (simplified inner expression).
        reduced_top_level = reduced_inner_expr.expr_hierarchy[0]
        eq1 = Equals(top_level, reduced_top_level)
        eq1.prove(assumptions, automation=False)
        eq2 = Equals(reduced_top_level, reduced_simplification.rhs)
        eq2.prove(assumptions, automation=False)
        simplification = eq1.apply_transitivity(eq2, assumptions)
    if not in_place and top_level == inner:
        # Store direct simplifications in the known_simplifications
        # dictionary for next time.
        Equals.known_simplifications[known_simplifications_key] = simplification
        if is_irreducible_value(value):
            # also store it in the known_evaluation_sets dictionary for
            # next time, since it evaluated to an irreducible value.
            Equals.known_evaluation_sets.setdefault(
                top_level, set()).add(simplification)
    return simplification


def evaluate_truth(expr, assumptions):
    '''
    Attempts to prove that the given expression equals TRUE under
    the given assumptions via proving the expression.
    Returns the resulting Judgment evaluation if successful.
    '''
    from proveit.logic import TRUE
    return Equals(expr, TRUE).prove(assumptions)


def evaluate_falsehood(expr, assumptions):
    '''
    Attempts to prove that the given expression equals FALSE under
    the given assumptions via disproving the expression.
    Returns the resulting Judgment evaluation if successful.
    '''
    from proveit.logic import FALSE
    return Equals(expr, FALSE).prove(assumptions)


class SimplificationError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message


class EvaluationError(SimplificationError):
    def __init__(self, expr, assumptions):
        self.message = ("Evaluation of %s under assumptions %s is not known"
                        % (expr, assumptions))

    def __str__(self):
        return self.message


class InversionError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message
