from proveit import (Judgment, as_expression, 
                     defaults, USE_DEFAULTS, ProofFailure,
                     UnsatisfiedPrerequisites,
                     Conditional, ExprTuple, equality_prover, InnerExpr,
                     InnerExprGenerator, free_vars)
from proveit.util import OrderedSet
from proveit import Literal, Operation, Lambda, ArgumentExtractionError
from proveit import TransitiveRelation, TransitivityException
from proveit import relation_prover, prover
from proveit.logic.irreducible_value import is_irreducible_value
from proveit import a, b, c, d, k, A, B, P, Q, f, n, x, y, z

class Equals(TransitiveRelation):
    # operator of the Equals operation
    _operator_ = Literal(string_format='=', theory=__file__)

    # Map Expressions to sets of Judgments of equalities that involve
    # the Expression on the left hand or right hand side.
    known_equalities = dict()

    # Map each Expression/defaults._simplification_directives_id 
    # combination to a single known_equality deemed to effect a 
    # simplification according to the simplification directives of 
    # the id.
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

    def __init__(self, a, b, *, styles=None):
        TransitiveRelation.__init__(self, Equals._operator_, a, b,
                                    styles=styles)
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
        also record the judgment in the Equals.known_evaluation_sets 
        dictionary, for use when the simplification or evaluation 
        method is called. Some side-effects derivations are also 
        attempted depending upon the form of this equality.
        '''
        from proveit.logic.booleans import TRUE, FALSE
        Equals.known_equalities.setdefault(
                self.lhs, OrderedSet()).add(judgment)
        Equals.known_equalities.setdefault(
                self.rhs, OrderedSet()).add(judgment)

        if is_irreducible_value(self.rhs):
            # With an irreducible right hand side, remember this as
            # an evaluation.
            assert isinstance(judgment.expr, Equals)
            Equals.known_evaluation_sets.setdefault(
                self.lhs, set()).add(judgment)

        if self.lhs == self.rhs:
            # Don't bother with side-effects for reflexive equalities.
            return

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

    @prover
    def conclude(self, **defaults_config):
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
                return self.conclude_boolean_equality()
            except ProofFailure:
                pass

        if (Implies(self.lhs, self.rhs).proven() and
                Implies(self.rhs, self.lhs).proven() and
                in_bool(self.lhs).proven() and
                in_bool(self.rhs).proven()):
            # There is mutual implication both sides are known to be
            # boolean.  Conclude equality via mutual implication.
            return Iff(self.lhs, self.rhs).derive_equality()
        
        if hasattr(self.lhs, 'deduce_equality'):
            # If there is a 'deduce_equality' method, use that.
            # The responsibility then shifts to that method for
            # determining what strategies should be attempted
            # (with the recommendation that it should not attempt
            # multiple non-trivial automation strategies), unless
            # NotImplementedError is raised.
            try:
                eq = self.lhs.deduce_equality(self)
                if eq.expr != self:
                    raise ValueError("'deduce_equality' not implemented "
                                     "correctly; must deduce the 'equality' "
                                     "that it is given if it can: "
                                     "'%s' != '%s'" % (eq.expr, self))
                return eq
            except (NotImplementedError, UnsatisfiedPrerequisites):
                # 'deduce_equality' not implemented for this 
                # particular case, so carry on with default approach.
                pass

        # Try to prove equality via standard TransitiveRelation
        # strategies (simplify both sides then try transitivity).
        return TransitiveRelation.conclude(self)

    @prover
    def conclude_via_direct_substitution(self, **defaults_config):
        '''
        Prove that this Equals expression is true by directly and
        greedily substituting sub-expressions that differ but are
        known to be equal.
        
        For example, we can prove
        f(g(a, b), h(c, d)) = f(g(a, b'), h(c, d'))
        if b=b' and d'=d.
        
        However, we cannot use this to prove
        f(g(a, b), h(c, d)) = f(g(a, b), h')
        by simply knowing d=d' and h(c, d')=h'. Rather, we must know
        h(c, d) = h'.
        '''
        from proveit import ExprRange
        if self.proven():
            # Already known.  Done.
            return self.prove()
        def raise_different_structures():
            raise ValueError("%s and %s have different structures "
                             "and cannot be equated via direct "
                             "substitution"%(self.lhs, self.rhs))            
        lhs_inner_gen = InnerExprGenerator(self.lhs)
        rhs_inner_gen = InnerExprGenerator(self.rhs)
        lambda_body = self.lhs
        lambda_parameters = []
        # Equating all entries (elements and ranges).
        all_equalities_lhs = []
        all_equalities_rhs = []
        replacements = []
        while True:
            try:
                next_inner_lhs = next(lhs_inner_gen)
            except StopIteration:
                try:
                    next_inner_rhs = next(rhs_inner_gen)
                except StopIteration:
                    break
                # lhs finished before rhs:
                raise_different_structures()
            try:
                next_inner_rhs = next(rhs_inner_gen)
            except StopIteration:
                # rhs finished before lhs:
                raise_different_structures()
            inner_expr_path = next_inner_lhs.inner_expr_path
            if (inner_expr_path != next_inner_rhs.inner_expr_path):
                raise_different_structures()

            # Check if the lhs/rhs InnerExpr objects correspond to the
            # same sub-expression or sub-expressions that are known to
            # be equal.
            lhs_sub_expr = next_inner_lhs.cur_sub_expr()
            rhs_sub_expr = next_inner_rhs.cur_sub_expr()
            assumptions = (next_inner_lhs.assumptions + 
                           tuple(next_inner_lhs.conditions))
            if lhs_sub_expr == rhs_sub_expr:
                # These sub-expressions are the same, so we can
                # skip over this entire branch.
                lhs_inner_gen.skip_over_branch()
                rhs_inner_gen.skip_over_branch()
                continue
            if (not isinstance(lhs_sub_expr, ExprRange) and
                not isinstance(lhs_sub_expr, ExprRange) and
                    Equals(lhs_sub_expr, rhs_sub_expr).proven(assumptions)):
                # These sub-expressions are known to be equal,
                # so let's replace the corresponding location
                # with a lambda parameter for our lambda expression.
                # Create the InnerExpr for the lambda_body for
                # the current inner expression path and use this
                # to create the new lambda_body and extend the
                # parameters.
                equality = Equals(lhs_sub_expr, rhs_sub_expr)
                lambda_body_inner_expr = InnerExpr(
                        lambda_body, inner_expr_path=inner_expr_path)
                params = free_vars(equality).intersection(
                        lambda_body_inner_expr.parameters)
                
                # If any assumptions are required that are introduced
                # by inner conditions, we need to equate Conditionals.
                inner_conditions = set(next_inner_lhs.conditions).intersection(
                        next_inner_rhs.conditions)
                conditions = []
                equality = equality.prove(assumptions=assumptions)
                for assumption in equality.assumptions:
                    if assumption in inner_conditions:
                        conditions.append(assumption)
                if len(conditions) > 0:
                    # Wrap sub-expressions in Conditionals.
                    lhs_sub_expr = Conditional(lhs_sub_expr, conditions)
                    rhs_sub_expr = Conditional(rhs_sub_expr, conditions)
                    # Make sure we replace the Conditional with
                    # its value where the condition is redundant.
                    replacement = lhs_sub_expr.satisfied_condition_reduction(
                            assumptions=conditions)
                    replacements.append(replacement)
                    replacement = rhs_sub_expr.satisfied_condition_reduction(
                            assumptions=conditions)
                    replacements.append(replacement)
                if len(params) > 0:
                    # We are substituting an inner scope with inner
                    # parameters.
                    # Generalize the equality over the parameters
                    # with appropriate conditions.
                    universal_eq = equality.generalize(params, 
                                                       conditions=conditions)
                    lhs_lambda = Lambda(params, lhs_sub_expr)
                    equality = lhs_lambda.substitution(universal_eq)
                elif len(conditions) > 0:
                    # No parameters but using Conditionals.
                    equality = Equals(lhs_sub_expr, rhs_sub_expr).prove()
                repl_lambda = lambda_body_inner_expr.repl_lambda(
                        params_of_param=params)
                lambda_body = repl_lambda.body
                lambda_parameters.extend(repl_lambda.parameters.entries)
                # We can skip over this branch now.
                lhs_inner_gen.skip_over_branch()
                rhs_inner_gen.skip_over_branch()
                all_equalities_lhs.append(equality.lhs)
                all_equalities_rhs.append(equality.rhs)
            else:
                # These sub-expressions are different. They could
                # have known equalities at a deeper level, but let's
                # make sure they have the same structure.
                if (lhs_sub_expr.core_info() != rhs_sub_expr.core_info() or
                        (lhs_sub_expr.num_sub_expr() != 
                         rhs_sub_expr.num_sub_expr())):
                    raise_different_structures()
        
        # Make the lambda map to use for substitutions.
        lambda_map = Lambda(lambda_parameters, lambda_body)
        if (len(all_equalities_lhs)==1 and 
                not isinstance(all_equalities_lhs[0], ExprRange)):
            # Just one, basic equality which we already know.
            return equality.substitution(lambda_map,
                             replacements=replacements)
        else:
            # Multi-operand substitution.
            from proveit.core_expr_types.tuples import tuple_eq_via_elem_eq
            tuple_eq = Equals(ExprTuple(*all_equalities_lhs),
                              ExprTuple(*all_equalities_rhs))
            return tuple_eq.substitution(
                    lambda_map, replacements=replacements)        

    """
    (0 = (t - ((t - 1) + 1)), 
     t - ((t - 1) + 1) if 0 = (t - ((t - 1) + 1))) = 
     (TRUE, 
      0 if 0 = (t - ((t - 1) + 1)))    
    
    {MULTI_QUDIT_GATE(CONTROL, {t - ((t - 1) + 1), t}) if 0 = (t - ((t - 1) + 1)). = 
    {MULTI_QUDIT_GATE(CONTROL, {0, t}) if TRUE.
    [{0 = (t - ((t - 1) + 1))} |- {t - ((t - 1) + 1) if 0 = (t - ((t - 1) + 1)). = (t - ((t - 1) + 1)), 
     {0 = (t - ((t - 1) + 1))} |- {0 if 0 = (t - ((t - 1) + 1)). = 0]
    """
 
    """
    Abandoning, but keeping a stub in case we want to revisit this:
    @prover
    def conclude_via_substitutions(self, *equalities, **defaults_config):
        '''
        Prove that this Equals expression is true by using the
        supplied proven equalities and performing substitutions.
        
        This is the "Equivalence Closure Problem" which Deepak Kapur
        has written papers on:
        Journal of Systems Science and Complexity volume 32, pages 317–355 (2019),
        https://10.4230/LIPIcs.FSCD.2021.15
        https://doi.org/10.1007/3-540-62950-5_59
        
        His algorithms are O(n log n) for binary functions and
        O(n^2) in general.
        '''
    """

    @staticmethod
    def WeakRelationClass():
        return Equals  # = is the strong and weak form of equality,

    @staticmethod
    def StrongRelationClass():
        return Equals  # = is the strong and weak form of equality,

    @staticmethod
    def known_relations_from_left(expr, assumptions_set):
        '''
        For each Judgment that is an Equals involving the given 
        expression on the left hand side, yield the Judgment and the 
        right hand side.
        '''
        for judgment in Equals.known_equalities.get(expr, frozenset()):
            if judgment.lhs == expr:
                if judgment.is_applicable(assumptions_set):
                    yield (judgment, judgment.rhs)

    @staticmethod
    def known_relations_from_right(expr, assumptions_set):
        '''
        For each Judgment that is an Equals involving the given 
        expression on the right hand side, yield the Judgment and the 
        left hand side.
        '''
        for judgment in Equals.known_equalities.get(expr, frozenset()):
            if judgment.rhs == expr:
                if judgment.is_applicable(assumptions_set):
                    yield (judgment, judgment.lhs)

    @prover
    def conclude_via_reflexivity(self, **defaults_config):
        '''
        Prove and return self of the form x = x.
        '''
        from . import equals_reflexivity
        assert self.lhs == self.rhs
        return equals_reflexivity.instantiate({x: self.lhs})

    @prover
    def derive_reversed(self, **defaults_config):
        '''
        From x = y derive y = x.  This derivation is an automatic 
        side-effect.
        '''
        from . import equals_reversal
        return equals_reversal.instantiate({x: self.lhs, y: self.rhs})

    def reversed(self):
        '''
        Return an Equals expression with the right side and left side 
        reversed from this one.  This is not a derivation: see 
        derive_reversed().
        '''
        return Equals(self.rhs, self.lhs)

    @staticmethod
    def yield_known_equal_expressions(expr, *, exceptions=None):
        '''
        Yield everything known to be equal to the given expression
        under the given assumptions directly or indirectly through 
        the transitive property of equality.
        If 'exceptions' are provided, disregard known equalities
        with expressions in the 'exceptions' set.
        '''
        assumptions = defaults.assumptions
        to_process = {expr}
        processed = set()
        while len(to_process) > 0:
            expr = to_process.pop()
            if (exceptions is not None and expr in exceptions):
                # Skip this 'exception'.
                continue
            yield expr
            processed.add(expr)
            if expr not in Equals.known_equalities:
                continue
            for known_equality in Equals.known_equalities[expr]:
                if known_equality.is_applicable(assumptions):
                    # A valid equality.  See if something is new.
                    for operand in known_equality.operands:
                        if operand not in processed:
                            to_process.add(operand)

    @prover
    def deduce_not_equals(self, **defaults_config):
        r'''
        Deduce x != y assuming not(x = y), where self is x=y.
        '''
        from .not_equals import NotEquals
        return NotEquals(self.lhs, self.rhs).conclude_as_folded()

    '''
    # This isn't right.
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
    '''

    @prover
    def apply_transitivity(self, other, **defaults_config):
        '''
        From x = y (self) and y = z (other) derive and return x = z.
        Also works more generally as long as there is a common side to 
        the equations.  If "other" is not an equality, reverse roles and
        call 'apply_transitivity' from the "other" side.
        '''
        from . import equals_transitivity
        other = as_expression(other)
        if not isinstance(other, Equals):
            # If the other relation is not "Equals", call from the "other"
            # side.
            return other.apply_transitivity(self)
        other_equality = other
        # We can assume that y=x will be a Judgment if x=y is a Judgment
        # because it is derived as a side-effect.
        if self.rhs == other_equality.lhs:
            return equals_transitivity.instantiate(
                {x: self.lhs, y: self.rhs, z: other_equality.rhs},
                preserve_all=True)
        elif self.rhs == other_equality.rhs:
            return equals_transitivity.instantiate(
                {x: self.lhs, y: self.rhs, z: other_equality.lhs},
                preserve_all=True)
        elif self.lhs == other_equality.lhs:
            return equals_transitivity.instantiate(
                {x: self.rhs, y: self.lhs, z: other_equality.rhs},
                preserve_all=True)
        elif self.lhs == other_equality.rhs:
            return equals_transitivity.instantiate(
                {x: self.rhs, y: self.lhs, z: other_equality.lhs},
                preserve_all=True)
        else:
            raise TransitivityException(
                None,
                defaults.assumptions,
                'Transitivity cannot be applied unless there is something in common in the equalities: %s vs %s' %
                (str(self), str(other)))

    @staticmethod
    @prover
    def relate_across_chain_transitively(*elements, **defaults_config):
        '''
        Use transitivity to relate the first element to the last
        element through a chain of relations through all of the 
        elements in order.
        '''
        from proveit import ExprRange
        num_elements = len(elements)
        if num_elements == 0:
            raise TransitivityException(
                None, defaults.assumptions, 
                'Empty chain of elements to relate')         
        if num_elements == 1:
            # Trivial case of a single element equal to itself.
            elem = elements[0]
            return Equals(elem, elem).conclude_via_reflexivity()
        elif num_elements == 2:
            # Simple case of a single relation.
            return Equals(*elements).prove()
        elif num_elements == 3:
            # x=y and y=z => x=z
            return Equals(*elements[:2]).apply_transitivity(
                    Equals(*elements[1:]))
        elif num_elements == 4:
            # a=b, b=c, c=d => a=d
            from . import four_chain_transitivity
            _a, _b, _c, _d = elements
            return four_chain_transitivity.instantiate(
                    {a:_a, b:_b, c:_c, d:_d})
        else:
            raise NotImplementedError(
                    "There are issues instantiating transitivity_chain "
                    "that need to be resolved; may require ExprRange "
                    "fixes") 
            """
            # A chain with more than 4 elements
            from proveit import IndexedVar
            from proveit.numbers import subtract, one, quick_simplified_index
            from proveit.numbers import Add
            from proveit.core_expr_types import x_1_to_np1
            from . import transitivity_chain
            _x = ExprTuple(*elements)
            if isinstance(_x[0], ExprRange) or isinstance(_x[1], ExprRange):
                raise NotImplementedError(
                        "'relate_across_chain_transitively' not implemented "
                        "when there is an ExprRange at as the first or last "
                        "of the entries, though it should be possible.")
            _np1 = quick_simplified_index(_x.num_elements())
            _n = quick_simplified_index(subtract(_x.num_elements(), one))
            x_full = ExprTuple(x_1_to_np1).basic_replaced({n:_n})
            # We really need to simplify instantiating this sort of 
            # thing. (see Issue #264)
            
            print(ExprRange(k, k, one, _np1).partition(_n))
            #print(ExprRange(k, k, one, _np1).partition(
            #        one).inner_expr().rhs[1].shifted(
            #                new_start=one))
            print(ExprRange(k, k, one, _np1).partition(one))
            x_split1 = x_full[0].partitioned(_n)
            #x_split2 = x_full[0].partition(one).inner_expr().rhs[1].shift(
            #        new_start=one).rhs # (x_1, x_{1+1}, ..., x_{n+1}) 
            x_split2 = x_full[0].partitioned(one)
            return transitivity_chain.instantiate(
                    {n:_n, x:_x, x_split1:_x, x_split2:_x})
            """
    
    @prover
    def derive_via_boolean_equality(self, **defaults_config):
        '''
        From A = TRUE derive A, or from A = FALSE derive Not(A).  
        This derivation is an automatic side-effect.
        Note, see derive_stmt_eq_true or Not.equate_negated_to_false 
        for the reverse process.
        '''
        from proveit.logic import TRUE, FALSE
        from proveit.logic.booleans import eq_true_elim
        from proveit.logic import Not
        if self.rhs == TRUE:
            return eq_true_elim.instantiate({A: self.lhs})  # A
        elif self.rhs == FALSE:
             # Not(A)
            return Not(self.lhs).conclude_via_falsified_negation()

    @prover
    def derive_contradiction(self, **defaults_config):
        '''
        From A=FALSE, and assuming A, derive FALSE.
        '''
        from proveit.logic import FALSE
        from . import contradiction_via_falsification
        if self.rhs == FALSE:
            return contradiction_via_falsification.instantiate(
                {A: self.lhs})
        raise ValueError(
            'Equals.derive_contradiction is only applicable if the '
            'right-hand-side is FALSE')

    @prover
    def affirm_via_contradiction(self, conclusion, **defaults_config):
        '''
        From (A=FALSE), derive the conclusion provided that the negated conclusion
        implies both (A=FALSE) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.booleans.implication import affirm_via_contradiction
        return affirm_via_contradiction(self, conclusion)

    @prover
    def deny_via_contradiction(self, conclusion, **defaults_config):
        '''
        From (A=FALSE), derive the negated conclusion provided that the conclusion
        implies both (A=FALSE) as well as A, and the conclusion is a Boolean.
        '''
        from proveit.logic.booleans.implication import deny_via_contradiction
        return deny_via_contradiction(self, conclusion)

    @prover
    def conclude_boolean_equality(self, **defaults_config):
        '''
        Prove and return self of the form 
            A=TRUE given A,
            A=FALSE given Not(A), or
            [Not(A)=FALSE] given A.
        '''
        from proveit.logic import TRUE, FALSE, Not
        from proveit.logic.booleans import eq_true_intro
        if self.rhs == TRUE:
            return eq_true_intro.instantiate({A: self.lhs})
        elif self.rhs == FALSE:
            if isinstance(self.lhs, Not):
                evaluation = self.lhs.evaluation()
                if evaluation.rhs == self.rhs:
                    return evaluation
            else:
                return Not(self.lhs).equate_negated_to_false()
        elif self.lhs == TRUE or self.lhs == FALSE:
            return Equals(self.rhs, self.lhs).conclude_boolean_equality(
                ).derive_reversed()
        raise ProofFailure(
            self,
            defaults.assumptions,
            "May only conclude via boolean equality if one side of the equality is TRUE or FALSE")

    @prover
    def derive_is_in_singleton(self, **defaults_config):
        '''
        From (x = y), derive (x in {y}).
        '''
        from proveit.logic.sets.enumeration import fold_singleton
        return fold_singleton.instantiate({x: self.lhs, y: self.rhs})

    @staticmethod
    def _lambda_expr(lambda_map, expr_being_replaced):
        from proveit import InnerExpr
        if isinstance(lambda_map, InnerExpr):
            lambda_map = lambda_map.repl_lambda()
        if not isinstance(lambda_map, Lambda):
            # as a default, do a global replacement
            lambda_map = Lambda.global_repl(lambda_map, expr_being_replaced)
        return lambda_map

    @prover # Note: this should NOT be an @equality_prover.
    def substitution(self, lambda_map, **defaults_config):
        '''
        From x = y, and given f(x), derive f(x)=f(y).  f(x) is provided 
        via lambda_map as a Lambda expression or an object that returns
        a Lambda expression when calling lambda_map() (see 
        proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression upon
        which to perform a global replacement of self.lhs.
        '''
        from proveit import Conditional
        from . import substitution

        if isinstance(lambda_map, Conditional):
            conditional = lambda_map
            if self.lhs == conditional.value:
                # Return the substitution equality for swapping out
                # the value of a conditional which may implicitly
                # assume that the condition is satisfied.
                return conditional.value_substitution(self)

        lambda_map = Equals._lambda_expr(lambda_map, self.lhs)
        
        if not lambda_map.parameters.is_single():
            # We must use operands_substitution for ExprTuple
            # substitution.
            from proveit.core_expr_types.operations import \
                operands_substitution, operands_substitution_via_tuple
            _n = lambda_map.parameters.num_elements()
            if self.proven():
                # If we know the tuples are equal, use the theorem
                # with this equality as a prerequisite.
                return operands_substitution_via_tuple.instantiate(
                    {n: _n, f: lambda_map, x: self.lhs, y: self.rhs})
            # Otherwise, we'll use the axiom in which the prerequisite
            # is that the individual elements are equal.
            return operands_substitution.instantiate(
                {n: _n, f: lambda_map, x: self.lhs, y: self.rhs})
        # Regular single-operand substitution:
        return substitution.instantiate(
            {f: lambda_map, x: self.lhs, y: self.rhs})

    @prover
    def sub_left_side_into(self, lambda_map, **defaults_config):
        '''
        From x = y, and given P(y), derive P(x) assuming P(y).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling 
        lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.rhs.
        '''
        from . import sub_left_side_into
        from . import (substitute_truth, substitute_in_true, 
                       substitute_falsehood, substitute_in_false)
        from proveit.logic import TRUE, FALSE
        lambda_map = Equals._lambda_expr(lambda_map, self.rhs)

        # Check if we want to use the reverse equality for a shorter
        # proof.
        reversed_eq = Equals(self.rhs, self.lhs)
        if reversed_eq.proven():
            if (reversed_eq.prove().proof().num_steps() <
                    self.prove().proof().num_steps()):
                # Reverse it for a shorter proof.
                return reversed_eq.sub_right_side_into(lambda_map)
        
        if not lambda_map.parameters.is_single():
            # We must use sub_in_left_operands for ExprTuple
            # substitution.
            from proveit.logic.equality import \
                sub_in_left_operands, sub_in_left_operands_via_tuple
            _n = lambda_map.parameters.num_elements()
            if self.proven():
                # If we know the tuples are equal, use the theorem
                # with this equality as a prerequisite.
                return sub_in_left_operands_via_tuple.instantiate(
                    {n: _n, P: lambda_map, x: self.lhs, y: self.rhs})                    
            return sub_in_left_operands.instantiate(
                {n: _n, P: lambda_map, x: self.lhs, y: self.rhs})
    
        try:
            # try some alternative proofs that may be shorter, if
            # they are usable
            if self.rhs == TRUE:
                # substitute_truth may provide a shorter proof
                # option
                substitute_truth.instantiate(
                    {x: self.lhs, P: lambda_map})
            elif self.lhs == TRUE:
                # substitute_in_true may provide a shorter proof
                # option
                substitute_in_true.instantiate(
                    {x: self.rhs, P: lambda_map})
            elif self.rhs == FALSE:
                # substitute_falsehood may provide a shorter proof
                # option
                substitute_falsehood.instantiate(
                    {x: self.lhs, P: lambda_map})
            elif self.lhs == FALSE:
                # substitute_in_false may provide a shorter proof
                # option
                substitute_in_false.instantiate(
                    {x: self.rhs, P: lambda_map})
        except BaseException:
            pass
        return sub_left_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map})

    @prover
    def sub_right_side_into(self, lambda_map, **defaults_config):
        '''
        From x = y, and given P(x), derive P(y) assuming P(x).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling
        lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from . import sub_right_side_into
        from . import (substitute_truth, substitute_in_true, 
                       substitute_falsehood, substitute_in_false)
        from proveit.logic import TRUE, FALSE
        
        # Check if we want to use the reverse equality for a shorter
        # proof.
        reversed_eq = Equals(self.rhs, self.lhs)
        if reversed_eq.proven():
            if (reversed_eq.prove().proof().num_steps() <
                    self.prove().proof().num_steps()):
                # Reverse it for a shorter proof.
                return reversed_eq.sub_left_side_into(lambda_map)
        
        lambda_map = Equals._lambda_expr(lambda_map, self.lhs)

        if not lambda_map.parameters.is_single():
            # We must use sub_in_right_operands for ExprTuple
            # substitution.
            from proveit.logic.equality import \
                sub_in_right_operands, sub_in_right_operands_via_tuple
            _n = lambda_map.parameters.num_elements()
            if self.proven():
                # If we know the tuples are equal, use the theorem
                # with this equality as a prerequisite.
                return sub_in_right_operands_via_tuple.instantiate(
                    {n: _n, P: lambda_map, x: self.lhs, y: self.rhs})
            return sub_in_right_operands.instantiate(
                {n: _n, P: lambda_map, x: self.lhs, y: self.rhs})
    
        try:
            # try some alternative proofs that may be shorter, if 
            # they are usable
            if self.lhs == TRUE:
                # substitute_truth may provide a shorter proof
                # options
                substitute_truth.instantiate(
                    {x: self.rhs, P: lambda_map})
            elif self.rhs == TRUE:
                # substitute_in_true may provide a shorter proof
                # options
                substitute_in_true.instantiate(
                    {x: self.lhs, P: lambda_map})
            elif self.lhs == FALSE:
                # substitute_falsehood may provide a shorter proof
                # options
                substitute_falsehood.instantiate(
                    {x: self.rhs, P: lambda_map})
            elif self.rhs == FALSE:
                # substitute_in_false may provide a shorter proof
                # options
                substitute_in_false.instantiate(
                    {x: self.lhs, P: lambda_map})
        except BaseException:
            pass
        return sub_right_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map})

    @prover
    def derive_right_via_equality(self, **defaults_config):
        '''
        From A = B, derive B (the Right-Hand-Side) assuming A.
        '''
        from . import rhs_via_equality
        return rhs_via_equality.instantiate({P: self.lhs, Q: self.rhs})

    @prover
    def derive_left_via_equality(self, **defaults_config):
        '''
        From A = B, derive A (the Right-Hand-Side) assuming B.
        '''
        from . import lhs_via_equality
        return lhs_via_equality.instantiate({P: self.lhs, Q: self.rhs})

    def other_side(self, expr):
        '''
        Returns the 'other' side of the of the equation if the given 
        expr is on one side.
        '''
        if expr == self.lhs:
            return self.rhs
        elif expr == self.rhs:
            return self.lhs
        raise ValueError(
            'The given expression is expected to be one of the sides of the equation')

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce and return that this equality statement is in the Boolean set.
        '''
        from . import equality_in_bool
        return equality_in_bool.instantiate({x: self.lhs, y: self.rhs},
                                            preserve_all=True)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Given equality operands that are the same or are irreducible
        values, return this expression equated to TRUE or FALSE.
        '''
        if self.lhs == self.rhs:
            # prove equality is true by reflexivity
            return evaluate_truth(self.conclude_via_reflexivity().expr)
        if (is_irreducible_value(self.lhs) and 
                is_irreducible_value(self.rhs)):
            # Irreducible values must know how to evaluate the equality
            # between each other, where appropriate.
            return self.lhs.eval_equality(self.rhs)
        if must_evaluate:
            # If we need an evaluation, this should do the trick:
            deduce_equal_or_not(self.lhs, self.rhs)
            return self.evaluation()
        return Operation.shallow_simplification(self)

    @staticmethod
    def get_known_evaluation(expr, *, automation=USE_DEFAULTS):
        '''
        Return an applicable evaluation (under current defaults) for 
        the given expression if one is known; otherwise return None.
        If automation is True, we are allow to derive
        an evaluation via transitivity with through any number of known 
        equalities, excluding equalities with any "preserved" 
        expressions (in defaults.preserved_exprs) whose evaluations
        are to be disregarded.
        '''
        if expr in Equals.known_evaluation_sets:
            evaluations = Equals.known_evaluation_sets[expr]
            candidates = []
            assumptions = defaults.assumptions
            assumptions_set = set(assumptions)
            for judgment in evaluations:
                if judgment.is_applicable(assumptions_set):
                    # Found existing evaluation suitable for the
                    # assumptions
                    candidates.append(judgment)
            if len(candidates) >= 1:
                # Return the "best" candidate with respect to fewest number
                # of steps.
                def min_key(judgment): return judgment.proof().num_steps()
                return min(candidates, key=min_key)
        if automation is USE_DEFAULTS:
            automation = defaults.conclude_automation
        if automation:
            # An evaluation isn't directly known, but we may know
            # something equal to this that has an evaluation and
            # therefore we have an evaluation by transitivity as long
            # as 'automation' is allowed.
            for eq_expr in Equals.yield_known_equal_expressions(
                    expr, exceptions=defaults.preserved_exprs):
                if eq_expr == expr: continue
                eq_evaluation = Equals.get_known_evaluation(
                        eq_expr, automation=False)
                if eq_evaluation is not None:
                    _eq = Equals(expr, eq_expr).conclude_via_transitivity()
                    return _eq.apply_transitivity(eq_evaluation)
        return None

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
                if known_equality.is_applicable(assumptions_set):
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

"""
def default_simplification(inner_expr, in_place=False, must_evaluate=False,
                           operands_only=False, assumptions=USE_DEFAULTS,
                           automation=USE_DEFAULTS):
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
    if automation is USE_DEFAULTS:
        automation = defaults.automation
    
    from proveit.logic import TRUE, FALSE
    from proveit.logic.booleans import true_axiom
    top_level = inner_expr.expr_hierarchy[0]
    inner = inner_expr.expr_hierarchy[-1]
    if operands_only:
        # Just do the reduction of the operands at the level below the
        # "inner expression"
        reduced_inner_expr = reduce_operands(
            inner_expr, in_place, must_evaluate)
        if in_place:
            try:
                return reduced_inner_expr.expr_hierarchy[0].prove(
                    automation=False)
            except BaseException:
                assert False
        try:
            eq = Equals(top_level, reduced_inner_expr.expr_hierarchy[0])
            return eq.prove(automation=False)
        except BaseException:
            assert False

    def inner_simplification(inner_equivalence):
        if in_place:
            return inner_equivalence.sub_right_side_into(inner_expr)
        return inner_equivalence.substitution(inner_expr)
    if is_irreducible_value(inner):
        return Equals(inner, inner).prove()
    assumptions_set = set(defaults.assumptions)

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
    assumptions_sorted = sorted(defaults.assumptions, 
                                key=lambda expr: hash(expr))
    known_simplifications_key = (inner, tuple(assumptions_sorted))

    if (must_evaluate and inner in Equals.known_evaluation_sets):
        evaluations = Equals.known_evaluation_sets[inner]
        candidates = []
        for judgment in evaluations:
            if judgment.is_applicable(assumptions_set):
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

    if not defaults.automation:
        msg = 'Unknown evaluation (without automation): ' + str(inner)
        raise SimplificationError(msg)

    # See if the expression is equal to something that has an evaluation
    # or is already known to be true.
    if inner in Equals.known_equalities:
        for known_eq in Equals.known_equalities[inner]:
            try:
                if known_eq.is_applicable(assumptions_set):
                    if in_place:
                        # Should first substitute in the known
                        # equivalence then simplify that.
                        if inner == known_eq.lhs:
                            known_eq.sub_right_side_into(inner_expr)
                        elif inner == known_eq.rhs:
                            known_eq.sub_left_side_into(inner_expr)
                    # Use must_evaluate=True.  Simply being equal to
                    # something simplified isn't necessarily the
                    # appropriate simplification for "inner" itself.
                    alt_inner = known_eq.other_side(inner).inner_expr()
                    equiv_simp = \
                        default_simplification(alt_inner, in_place=in_place,
                                               must_evaluate=True,
                                               automation=False)
                    if in_place:
                        # Returns Judgment with simplification:
                        return equiv_simp
                    inner_equiv = known_eq.apply_transitivity(equiv_simp)
                    if inner == top_level:
                        return inner_equiv
                    return inner_equiv.substitution(inner_expr)
            except SimplificationError:
                pass
    # try to simplify via reduction
    if not isinstance(inner, Operation):
        if must_evaluate:
            raise EvaluationError('Unknown evaluation: ' + str(inner))
        else:
            # don't know how to simplify, so keep it the same
            return inner_simplification(Equals(inner, inner).prove())
    reduced_inner_expr = reduce_operands(inner_expr, in_place, must_evaluate)
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
        inner_equiv = inner.evaluation()
    else:
        inner_equiv = inner.simplification()
    value = inner_equiv.rhs
    if value == TRUE:
        # Attempt to evaluate via proving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluate_truth(inner)
        except BaseException:
            pass
    if value == FALSE:
        # Attempt to evaluate via disproving the expression;
        # This should result in a shorter proof if allowed
        # (e.g., if theorems are usable).
        try:
            evaluate_falsehood(inner)
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
        eq1.prove(automation=False)
        eq2 = Equals(reduced_top_level, reduced_simplification.rhs)
        eq2.prove(automation=False)
        simplification = eq1.apply_transitivity(eq2)
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
"""

@prover
def evaluate_truth(expr, **defaults_config):
    '''
    Attempts to prove that the given expression equals TRUE under
    the given assumptions via proving the expression.
    Returns the resulting Judgment evaluation if successful.
    '''
    from proveit.logic import TRUE
    return Equals(expr, TRUE).conclude_boolean_equality()

@prover
def evaluate_falsehood(expr, **defaults_config):
    '''
    Attempts to prove that the given expression equals FALSE under
    the given assumptions via disproving the expression.
    Returns the resulting Judgment evaluation if successful.
    '''
    from proveit.logic import FALSE
    return Equals(expr, FALSE).conclude_boolean_equality()

@prover
def deduce_equal_or_not(lhs, rhs, **defaults_config):
    '''
    Prove and return that lhs=rhs or lhs≠rhs or raise an 
    UnsatisfiedPrerequisites or NotImplementedError
    if neither of these is readily known.
    '''
    from proveit.logic import NotEquals
    if Equals(lhs, rhs).proven():
        return Equals(lhs, rhs).prove()
    if lhs == rhs:
        return Equals(lhs, rhs).conclude_via_reflexivity()
    if NotEquals(lhs, rhs).proven():
        return NotEquals(lhs, rhs).prove()
    if hasattr(lhs, 'deduce_equal_or_not'):
        return lhs.deduce_equal_or_not(rhs)
    raise UnsatisfiedPrerequisites(
            "We cannot readily prove whether or not %s=%s"
            %(lhs, rhs))

def evaluation_or_simplification(expr, return_none_if_trivial=False):
    '''
    Return a nontrivial evaluation of the given expression if possible;
    otherwise return a nontrivial simplification if possible.  If
    we can't obtain one or the expression is already irreducible or
    simplified, return the trivial reflection or None if
    return_none_if_trivial is True.
    '''
    def trivial_form():
        if return_none_if_trivial:
            return None
        return Equals(expr, expr).conclude_via_reflexivity()
    if is_irreducible_value(expr):
        # This is already irreducible; nothing more to do.
        return trivial_form()
    try:
        # First try an evaluation -- this is best and it
        # should fail quickly when it can't be done.
        return expr.evaluation()
    except (SimplificationError, ProofFailure,
            UnsatisfiedPrerequisites, NotImplementedError):
        pass
    try:
        # If we weren't able to do an evaluation, try a
        # simplification.
        simplification = expr.simplification()
        if simplification.lhs != simplification.rhs:
            return simplification
    except (SimplificationError, ProofFailure,
            UnsatisfiedPrerequisites, NotImplementedError):
        pass
    return trivial_form()


class SimplificationError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message


class EvaluationError(SimplificationError):
    def __init__(self, expr, assumptions=None):
        if assumptions is None:
            assumptions = defaults.assumptions
        self.message = ("Evaluation of %s under assumptions %s is not known"
                        % (expr, assumptions))

    def __str__(self):
        return self.message


class InversionError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message
