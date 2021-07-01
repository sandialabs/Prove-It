from proveit import (Expression, Literal, Operation, Conditional,
                     defaults, USE_DEFAULTS, ProofFailure, InnerExpr,
                     prover, equality_prover, SimplificationDirectives,
                     TransRelUpdater)
from proveit.logic.equality import SimplificationError
from proveit import j, k, l, m, n, A, B, C, D, E, F, G
from proveit.logic.booleans.booleans import in_bool
from proveit.abstract_algebra.generic_methods import apply_commutation_thm, apply_association_thm, apply_disassociation_thm, group_commutation, group_commute


class And(Operation):
    # The operator of the And operation
    _operator_ = Literal(
        string_format='and',
        latex_format=r'\land',
        theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
        ungroup=True)

    def __init__(self, *operands, styles=None):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        Operation.__init__(self, And._operator_, operands, styles=styles)

    def _formatted(self, format_type, **kwargs):
        '''
        Override Operation._formatted when formatting a conjunction
        of relations as a total ordering.
        '''
        if self.get_style('as_total_ordering', 'False') == 'True':
            self._check_total_ordering_applicability()
            relations = self.operands.entries
            operands = [rel.lhs for rel in relations] + [relations[-1].rhs]
            formatted_operators = [
                    rel.operator.formatted(format_type) if
                    rel.get_style('direction', 'normal') == 'normal'
                    else rel.__class__.reversed_operator_str(format_type)
                    for rel in relations]
            return Operation._formattedOperation(
                format_type,
                formatted_operators,
                operands,
                wrap_positions=self.wrap_positions(),
                justification=self.get_style('justification'),
                **kwargs)
        else:
            # Just use the default Operation._formatted method.
            return Operation._formatted(self, format_type, **kwargs)
    
    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        call_strs = Operation.remake_with_style_calls(self)
        if self.get_style('as_total_ordering', 'False') == 'True':
            call_strs.append('with_total_ordering_style()')
        return call_strs

    def _check_total_ordering_applicability(self):
        '''
        Check to see if the total ordering style is
        applicable, raising an exception otherwise.
        '''
        from proveit.relation import TransitiveRelation
        relations = self.operands.entries
        for relation in relations:
            if not isinstance(relation, TransitiveRelation):
                raise TypeError(
                    "Can only to effect a total ordering style on "
                    "a conjunction of TransitiveRelation objects, "
                    "not %s of type %s"
                    %(relation, relation.__class__))
        for rel1, rel2 in zip(relations[:-1], relations[1:]):
            if rel1.rhs != rel2.lhs:
                raise ValueError(
                    "Consecutive total ordering relations must "
                    "match rhs to lhs: %s and %s do not match"
                    %(rel1, rel2))
    
    def style_options(self):
        '''
        Return the StyleOptions object for this And expression.
        '''
        style_options = Operation.style_options(self)
        try:
            self._check_total_ordering_applicability()
            style_options.add_option(
                    name = "as_total_ordering",
                    description = ("When 'True', style the conjunction as a "
                                   "total ordering (e.g. x < y < z from "
                                   "(x < y) and (y < z))"),
                    default = None,
                    related_methods = ('with_total_ordering_style',))
        except (TypeError, ValueError):
            pass # total ordering is not applicable
        return style_options

    def with_total_ordering_style(self):
        '''
        Use the total ordering style.
        '''
        self._check_total_ordering_applicability()
        return self.with_styles(as_total_ordering='True')

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to automatically conclude this conjunction via composing 
        the constituents.
        That is, conclude some A and B and ... and Z via
        A, B, ..., Z individually.
        '''
        from proveit import ExprRange
        from . import true_and_true
        if self == true_and_true.expr:
            return true_and_true  # simple special case
        if (self.operands.num_entries() == 1 and
                isinstance(self.operands[0], ExprRange) and
                self.operands[0].is_parameter_independent):
            return self.conclude_as_redundant()
        return self.conclude_via_composition()

    @prover
    def conclude_negation(self, **defaults_config):
        # Created by JML on 6/24/19
        from . import (
            true_and_false_negated,
            false_and_true_negated,
            false_and_false_negated,
            nand_if_neither,
            nand_if_left_but_not_right,
            nand_if_right_but_not_left)
        from proveit.logic import Not
        not_self = Not(self)
        if not_self in {
                true_and_false_negated.expr,
                false_and_true_negated.expr,
                false_and_false_negated.expr}:
            # should be disproven via one of the imported theorems as a
            # simple special case
            return not_self.prove()
            # Prove that the conjunction is true by proving that one of 
            # its operands is false and then negate it.
        # In the first attempt, don't use automation to prove any of the
        # operands so that
        # we don't waste time trying to prove operands when we already 
        # know one to be false
        use_automation_possibilities = (
                [False, True] if defaults.automation else [False])
        for use_automation_for_operand in use_automation_possibilities:
            disproven_operand_indices = []
            for _k, operand in enumerate(self.operands):
                try:
                    operand.disprove(automation=use_automation_for_operand)
                    disproven_operand_indices.append(_k)
                    # possible way to prove it
                    self.conclude_negation_via_example(operand)
                except ProofFailure:
                    pass
            if self.operands.is_double() and len(disproven_operand_indices) > 0:
                # One or both of the two operands were known to be true 
                # (without automation).
                # Try a possibly simpler proof than 
                # conclude_negation_via_example.
                try:
                    if len(disproven_operand_indices) == 2:
                        return nand_if_neither.instantiate(
                            {A: self.operands[0], B: self.operands[1]})
                    elif disproven_operand_indices[0] == 0:
                        return nand_if_right_but_not_left.instantiate(
                            {A: self.operands[0], B: self.operands[1]})
                    else:
                        return nand_if_left_but_not_right.instantiate(
                            {A: self.operands[0], B: self.operands[1]})
                except BaseException:
                    pass
            if len(disproven_operand_indices) > 0:
                # Not(self) should have been proven via
                # conclude_negation_via_example above
                try:
                    return not_self.prove(automation=False)
                except BaseException:
                    # If it wasn't proven via 
                    # conclude_negation_via_example, let's
                    # call it again to raise the appropriate exception.
                    operand = self.operands[disproven_operand_indices[0]]
                    return self.conclude_negation_via_example(operand)
        raise ProofFailure(not_self, defaults.assumptions,
                           "Unable to conclude the negated conjunction; "
                           "we could not disprove any of the conjunction "
                           "operands.")

    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically.
        '''

        from proveit.logic import Not
        from proveit import ExprRange
        if self.operands.num_entries() == 0:
            return  # No side-effects needed for [And]().
        if self.operands.is_double():
            if self.operands[1] == Not(self.operands[0]):
                # (A or not(A)) is an unfolded Boolean
                return  # stop to avoid infinite recursion.
        yield self.derive_in_bool
        for i, operand in enumerate(self.operands):
            if not isinstance(operand, ExprRange):
                yield lambda : self.derive_any(i)

        # yield self.derive_commutation

    def negation_side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for 
        Not(A and B and .. and .. Z).
        '''
        from proveit.logic import Not, Or
        yield self.derive_in_bool  # (A and B and ... and Z) in Boolean
        # implemented by JML on 7/2/19
        # If all of the operands are negated call the disjunction form of
        # DeMorgan's
        if all(isinstance(operand, Not) for operand in self.operands):
            demorgan_or = Or(*[operand.operand for operand in self.operands])
            yield demorgan_or.conclude_via_demorgans

    def in_bool_side_effects(self, judgment):
        '''
        From (A and B and .. and Z) in Boolean deduce
        (A in Boolean), (B in Boolean), ... (Z in Boolean).
        '''
        for i in range(self.operands.num_entries()):
            yield lambda : self.deduce_part_in_bool(i)

    @prover
    def derive_in_bool(self, **defaults_config):
        '''
        From (A and B and ... and Z) derive 
        [(A and B and ... and Z) in Boolean].
        '''
        from proveit.logic.booleans import in_bool_if_true
        return in_bool_if_true.instantiate({A: self})

    @prover
    def derive_any(self, index_or_expr, **defaults_config):
        r'''
        From (A and ... and X and ... and Z) derive X.
        index_or_expr specifies X, either by index or the expression.
        '''
        from proveit import ExprRange
        from . import (any_from_and, left_from_and, right_from_and,
                                 from_unary_and)
        if isinstance(index_or_expr, int):
            idx = index_or_expr
        else:
            idx = list(self.operands).index(index_or_expr)
        if idx < 0 or idx >= self.operands.num_entries():
            raise IndexError("Operand out of range: " + str(idx))
        has_range_operands = any(isinstance(operand, ExprRange)
                                 for operand in self.operands)
        if self.operands.num_entries() == 1 and not has_range_operands:
            # Derive A from And(A).
            return from_unary_and.instantiate({A: self.operands[0]})
        if self.operands.is_double() and not has_range_operands:
            # Two operand special case:
            if idx == 0:
                return left_from_and.instantiate(
                    {A: self.operands[0], B: self.operands[1]})
            elif idx == 1:
                return right_from_and.instantiate(
                    {A: self.operands[0], B: self.operands[1]})
        else:
            # Multiple operands.
            from proveit.core_expr_types import Len
            operand_to_extract = self.operands[idx]
            if isinstance(operand_to_extract, ExprRange):
                # Derive the conjunction of a range of operands.
                return self.derive_some_from_and(idx)
            else:
                A_sub = self.operands[:idx]
                B_sub = self.operands[idx]
                C_sub = self.operands[idx + 1:]
                m_val = Len(A_sub).computed()
                n_val = Len(C_sub).computed()
                return any_from_and.instantiate(
                    {m: m_val, n: n_val, A: A_sub, B: B_sub, C: C_sub})

    @prover
    def derive_some(self, start_idx, end_idx=None, **defaults_config):
        '''
        From (A and ... and B and ... Z) derive a range of the
        conjunction, such as (C and ... and F).  Specify the range
        by providing the start and end indices (inclusive) w.r.t.
        operand entries.  If end_idx is not provided, it defaults
        to start_idx for a single entry which should be an ExprRange.
        '''
        from proveit.core_expr_types import Len
        from proveit.logic.booleans.conjunction import some_from_and
        if end_idx is None:
            end_idx = start_idx
        A_sub = self.operands[:start_idx]
        B_sub = self.operands[start_idx:end_idx + 1]
        C_sub = self.operands[end_idx + 1:]
        l_val = Len(A_sub).computed()
        m_val = Len(B_sub).computed()
        n_val = Len(C_sub).computed()
        return some_from_and.instantiate({l: l_val, m: m_val, n: n_val,
                                          A: A_sub, B: B_sub, C: C_sub})

    @prover
    def derive_left(self, **defaults_config):
        r'''
        From A and B derive A.
        '''
        if self.operands.num_entries() != 2:
            raise Exception(
                'derive_left only applicable for binary conjunction operations')
        return self.derive_any(0)

    @prover
    def derive_right(self, **defaults_config):
        r'''
        From A and B derive B.
        '''
        if self.operands.num_entries() != 2:
            raise Exception(
                'derive_right only applicable for binary conjunction operations')
        return self.derive_any(1)

    @equality_prover('unary_reduced', 'unary_reduce')
    def unary_reduction(self, **defaults_config):
        from proveit.logic.booleans.conjunction import \
            unary_and_reduction
        if not self.operands.is_single():
            raise ValueError("Expression must have a single operand in "
                             "order to invoke unary_reduction")
        operand = self.operands[0]
        return unary_and_reduction.instantiate({A: operand})

    @prover
    def conclude_via_composition(self, **defaults_config):
        '''
        Prove and return some (A and B ... and ... Z) via 
        A, B, ..., Z each proven individually.
        See also the compose method to do this constructively.
        '''
        return compose(*self.operands.entries)

    @prover
    def deduce_left_in_bool(self, **defaults_config):
        '''
        Deduce A in Boolean from (A and B) in Boolean.
        '''
        from . import left_in_bool
        if self.operands.is_double():
            return left_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]})
        raise ValueError("'deduce_left_in_bool' not applicable to %s, "
                         "only applicable when there are two operands."
                         %self)

    @prover
    def deduce_right_in_bool(self, **defaults_config):
        '''
        Deduce B in Boolean from (A and B) in Boolean.
        '''
        from . import right_in_bool
        if self.operands.is_double():
            return right_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]})
        raise ValueError("'deduce_right_in_bool' not applicable to %s, "
                         "only applicable when there are two operands."
                         %self)

    @prover
    def deduce_part_in_bool(self, index_or_expr, **defaults_config):
        '''
        Deduce X in Boolean from (A and B and .. and X and .. and Z) in Boolean
        provided X by expression or index number.
        '''
        from . import each_is_bool
        idx = (index_or_expr if isinstance(index_or_expr, int) else 
               self.operands.entries.index(index_or_expr))
        if idx < 0 or idx >= self.operands.num_entries():
            raise IndexError("Operand out of range: " + str(idx))
        if self.operands.is_double():
            if idx == 0:
                return self.deduce_left_in_bool()
            elif idx == 1:
                return self.deduce_right_in_bool()
        else:
            _A = self.operands[:idx]
            _B = self.operands[idx]
            _C = self.operands[idx + 1:]
            _m = _A.num_elements()
            _n = _C.num_elements()
            return each_is_bool.instantiate(
                    {m: _m, n: _n, A: _A, B: _B, C: _C})

    @prover
    def conclude_via_demorgans(self, **defaults_config):
        '''
        # created by JML 6/28/19
        From A and B and C conclude Not(Not(A) or Not(B) or Not(C))
        '''
        from . import demorgans_law_or_to_and, demorgans_law_or_to_and_bin
        if self.operands.is_double():
            return demorgans_law_or_to_and_bin.instantiate(
                {A: self.operands[0], B: self.operands[1]})
        else:
            _A = self.operands
            _m = _A.num_elements()
            return demorgans_law_or_to_and.instantiate({m: _m, A: _A})

    @prover
    def conclude_negation_via_example(self, false_operand, **defaults_config):
        '''
        From one false operand, conclude the negation of this 
        conjunction.  Requires all of the operands to be in the
        BOOLEAN set.
        '''
        from . import nand_if_not_one, nand_if_not_left, nand_if_not_right
        index = self.operands.index(false_operand)
        if self.operands.is_double():
            if index == 0:
                return nand_if_not_left.instantiate(
                    {A: self.operands[0], B: self.operands[1]})
            elif index == 1:
                return nand_if_not_right.instantiate(
                    {A: self.operands[0], B: self.operands[1]})
        _A = self.operands[:index]
        _B = self.operands[index]
        _C = self.operands[index + 1:]
        _m = _A.num_elements()
        _n = _C.num_elements()
        return nand_if_not_one.instantiate(
                {m: _m, n: _n, A: _A, B: _B, C: _C})

    @prover
    def conclude_as_redundant(self, **defaults_config):
        '''
        Conclude an expression of the form
        A and ..n repeats.. and A
        given n in Natural and A is TRUE.
        '''
        from proveit import ExprRange
        from proveit.numbers import one
        from . import redundant_conjunction
        if (self.operands.num_entries() != 1 or
                not isinstance(self.operands[0], ExprRange) or
                not self.operands[0].is_parameter_independent):
            raise ValueError("`And.conclude_as_redundant` only allowed for a "
                             "conjunction of the form "
                             "A and ..n repeats.. and A, not %s" % self)
        if self.operands[0].start_index != one:
            raise NotImplementedError(
                "'conclude_as_redundant' only implemented "
                "when the start index is 1.  Just need to "
                "do an ExprRange shift to implement it more "
                "completely")
        _A = self.operands[0].body
        return redundant_conjunction.instantiate(
            {n: self.operands[0].end_index, A: _A})
    
    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Attempt to determine whether this conjunction, with
        simplified operands, evaluates to TRUE or FALSE under the given 
        assumptions.  If all operands have simplified to TRUE,
        the conjunction is TRUE.  If any of the operands have
        simplified to FALSE, the conjunction may be FALSE (if the
        other operands are provably Boolean).
        If it can't be evaluated, and must_evaluate is False,
        ungroup nested conjunctions if that is an active
        simplification direction.  Also, if applicable, perform 
        a unary reduction: And(A) = A.
        '''
        from proveit.logic import (Equals, FALSE, TRUE, EvaluationError,
                                   is_irreducible_value)
        # load in truth-table evaluations
        from . import and_t_t, and_t_f, and_f_t, and_f_f
        
        if self.operands.num_entries() == 0:
            from proveit.logic.booleans.conjunction import \
                empty_conjunction_eval
            # And() = TRUE
            return empty_conjunction_eval
        
        # Check whether or not all of the operands are TRUE
        # or any are FALSE.
        all_are_true = True
        for operand in self.operands:
            if operand != TRUE:
                all_are_true = False
            if operand == FALSE:
                # If any simplified operand is FALSE, the conjunction 
                # may only evaluate to FALSE if it can be evaluated.
                # Only use automation here if 'must_evaluate' is True.
                self.conclude_negation(automation=must_evaluate)
                return Equals(self, FALSE).prove()
        
        # If all of the operands are TRUE, we can prove that the
        # conjunction is equal to TRUE.
        if all_are_true:
            self.conclude()
            return Equals(self, TRUE).prove()
        
        if must_evaluate:
            if not all(is_irreducible_value(operand) for 
                       operand in self.operands):
                # The simplification of the operands may not have
                # worked hard enough.  Let's work harder if we
                # must evaluate.
                for operand in self.operands:
                    if not is_irreducible_value(operand):
                        operand.evaluation()
                return self.evaluation()
            # Can't evaluate the conjunction if no operand was
            # FALSE but they aren't all TRUE.
            raise EvaluationError(self)
    
        if self.operands.is_single():
            # And(A) = A
            return self.unary_reduction()

        expr = self
        # for convenience updating our equation
        eq = TransRelUpdater(expr)

        if And._simplification_directives_.ungroup:
            # ungroup the expression (disassociate nested conjunctions).
            _n = 0
            length = expr.operands.num_entries() - 1
            # loop through all operands
            while _n < length:
                operand = expr.operands[_n]
                if isinstance(operand, And):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, auto_simplify=False))
                length = expr.operands.num_entries()
                _n += 1

        return Expression.shallow_simplification(self)

    @prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Attempt to deduce, then return, that this 'and' expression is 
        in the BOOLEAN set.
        '''

        from . import binary_closure, closure
        if self.operands.is_double():
            return binary_closure.instantiate(
                {A: self.operands[0], B: self.operands[1]})
        _A = self.operands
        _m = _A.num_elements()
        return closure.instantiate({m: _m, A: _A})

    @equality_prover('commuted', 'commute')
    def commutation(self, init_idx=None, final_idx=None,
                    **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, (A and B and ... and Y and Z) = (A and ... and Y and B and Z)
        via init_idx = 1 and final_idx = -2.
        '''
        from . import commutation, leftward_commutation, rightward_commutation
        return apply_commutation_thm(
            self,
            init_idx,
            final_idx,
            commutation,
            leftward_commutation,
            rightward_commutation)

    @equality_prover('group_commuted', 'group_commute')
    def group_commutation(self, init_idx, final_idx, length,
                          disassociate=True, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operands
        at indices [init_idx, init_idx+length) have been moved to [final_idx. final_idx+length).
        It will do this by performing association first.  If disassociate is True, it
        will be disassociated afterwards.
        '''
        return group_commutation(
            self,
            init_idx,
            final_idx,
            length,
            disassociate)

    @prover
    def commute(self, init_idx=None, final_idx=None, **defaults_config):
        '''
        From self, derive and return a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, given (A and B and ... and Y and Z) derive 
        (A and ... and Y and B and Z)
        via init_idx = 1 and final_idx = -2.
        '''
        from . import commute, leftward_commute, rightward_commute
        return apply_commutation_thm(
            self, init_idx, final_idx, commute,
            leftward_commute, rightward_commute)

    @prover
    def group_commute(self, init_idx, final_idx, length, disassociate=True,
                      **defaults_config):
        '''
        Given self, deduce and return a form in which the operands
        at indices [init_idx, init_idx+length) have been moved to 
        [final_idx. final_idx+length).
        It will do this by performing association first. 
        If disassocate is True, it will be disassociated afterwards.
        '''
        return group_commute(
            self, init_idx, final_idx, length, disassociate)

    @equality_prover('associated', 'associate')
    def association(self, start_idx, length, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal to 
        a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, 
            (A and B and ... and Y and Z) = 
            (A and B ... and (L and ... and M) and ... and Y and Z)
        '''
        from . import association
        return apply_association_thm(
            self, start_idx, length, association)

    @prover
    def associate(self, start_idx, length, **defaults_config):
        '''
        From self, derive and return a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, from (A and B and ... and Y and Z) derive
        (A and B ... and (L and ... and M) and ... and Y and Z).
        '''
        from . import associate
        return apply_association_thm(
            self, start_idx, length, associate)

    @equality_prover('disassociated', 'disassociate')
    def disassociation(self, idx, **defaults_config):
        '''
        Given Boolean operands, deduce that this expression is equal to
        a form in which the operand  at index idx is no longer grouped 
        together.
        For example, 
            (A and B ... and (L and ... and M) and ... and Y and Z) = 
            (A and B and ... and Y and Z)
        '''
        from . import disassociation
        return apply_disassociation_thm(self, idx, disassociation)

    @prover
    def disassociate(self, idx, **defaults_config):
        '''
        From self, derive and return a form in which the operand
        at the given index is ungrouped.
        For example, from 
        (A and B ... and (L and ... and M) and ... and Y and Z)
        derive (A and B and ... and Y and Z).
        '''
        from . import disassociate
        return apply_disassociation_thm(self, idx, disassociate)


@prover
def compose(*expressions, **defaults_config):
    '''
    Returns [A and B and ...], the And operator applied to the 
    collection of given arguments, derived from each separately.
    '''
    from proveit._core_.expression.composite import composite_expression
    expressions = composite_expression(expressions)
    if expressions.num_entries() == 0:
        from proveit.logic.booleans.conjunction import \
            empty_conjunction
        return empty_conjunction
    if expressions.is_double():
        from . import and_if_both
        return and_if_both.instantiate(
            {A: expressions[0], B: expressions[1]}, auto_simplify=False)
    else:
        from . import and_if_all
        _m = expressions.num_elements()
        return and_if_all.instantiate({m: _m, A: expressions}, auto_simplify=False)
