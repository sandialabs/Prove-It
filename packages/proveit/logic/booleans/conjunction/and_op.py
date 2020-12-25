from proveit import (Literal, Operation, Conditional,
                     defaults, USE_DEFAULTS, ProofFailure, InnerExpr)
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

    def __init__(self, *operands):
        r'''
        And together any number of operands: :math:`A \land B \land C`
        '''
        Operation.__init__(self, And._operator_, operands)

    def auto_reduction(self, assumptions=USE_DEFAULTS):
        '''
        Automatically reduce "And() = TRUE" and "And(a) = a".
        '''
        if len(self.operands) == 0:
            from proveit.logic.booleans.conjunction import \
                empty_conjunction_eval
            if empty_conjunction_eval.is_usable():
                return empty_conjunction_eval
        elif self.operands.is_singular():
            try:
                return self.unary_reduction(assumptions)
            except BaseException:
                # Cannot do the reduction if the operand is not known
                # to be a boolean.
                pass

    def conclude(self, assumptions):
        '''
        Try to automatically conclude this conjunction via composing the constituents.
        That is, conclude some :math:`A \land B \and ... \land Z` via
        :math:'A', :math:'B', ..., :math:'Z' individually.
        '''
        from proveit import ExprRange
        from . import true_and_true
        if self == true_and_true.expr:
            return true_and_true  # simple special case
        if (len(self.operands) == 1 and
                isinstance(self.operands[0], ExprRange) and
                self.operands[0].is_parameter_independent):
            return self.conclude_as_redundant(assumptions)
        return self.conclude_via_composition(assumptions)

    def conclude_negation(self, assumptions=USE_DEFAULTS):
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
            # should be disproven via one of the imported theorems as a simple
            # special case
            return not_self.prove()
            # Prove that the conjunction is true by proving that one of its operands is false and then negate it.
        # In the first attempt, don't use automation to prove any of the operands so that
        # we don't waste time trying to prove operands when we already know one
        # to be false
        for use_automation_for_operand in [False, True]:
            disproven_operand_indices = []
            for _k, operand in enumerate(self.operands):
                try:
                    operand.disprove(
                        assumptions, automation=use_automation_for_operand)
                    disproven_operand_indices.append(_k)
                    # possible way to prove it
                    self.conclude_via_example(operand, assumptions=assumptions)
                except ProofFailure:
                    pass
            if len(self.operands) == 2 and len(disproven_operand_indices) > 0:
                # One or both of the two operands were known to be true (without automation).
                # Try a possibly simpler proof than conclude_via_example.
                try:
                    if len(disproven_operand_indices) == 2:
                        return nand_if_neither.instantiate(
                            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
                    elif disproven_operand_indices[0] == 0:
                        return nand_if_right_but_not_left.instantiate(
                            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
                    else:
                        return nand_if_left_but_not_right.instantiate(
                            {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
                except BaseException:
                    pass
            if len(disproven_operand_indices) > 0:
                # Not(self) should have been proven via
                # conclude_via_example above
                try:
                    return not_self.prove(assumptions, automation=False)
                except BaseException:
                    # If it wasn't proven via conclude_via_example, let's
                    # call it again to raise the appropriate exception.
                    operand = self.operands[disproven_operand_indices[0]]
                    return self.conclude_via_example(
                        operand, assumptions=assumptions)
        raise ProofFailure(not_self, assumptions,
                           "Unable to conclude the negated conjunction; "
                           "we could not disprove any of the conjunction "
                           "operands.")

    def side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically.
        '''

        from proveit.logic import Not
        if len(self.operands) == 0:
            return  # No side-effects needed for [And]().
        if len(self.operands) == 2:
            if self.operands[1] == Not(self.operands[0]):
                # (A or not(A)) is an unfolded Boolean
                return  # stop to avoid infinite recursion.
        yield self.derive_in_bool
        yield self.derive_parts
        # yield self.derive_commutation

    def negation_side_effects(self, judgment):
        '''
        Side-effect derivations to attempt automatically for Not(A and B and .. and .. Z).
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
        From (A and B and .. and Z) in Boolean deduce (A in Boolean), (B in Boolean), ...
        (Z in Boolean).
        '''
        yield self.deduce_parts_in_bool

    def derive_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        From (A and B and ... and Z) derive [(A and B and ... and Z) in Boolean].
        '''
        return in_bool(self).prove(assumptions=assumptions)

    def derive_parts(self, assumptions=USE_DEFAULTS):
        r'''
        From (A and B and ... and Z)` derive each operand:
        A, B, ..., Z.
        '''
        from proveit import ExprRange
        for i, operand in enumerate(self.operands):
            if isinstance(operand, ExprRange):
                pass
            else:
                self.derive_any(i, assumptions)

    def derive_any(self, index_or_expr, assumptions=USE_DEFAULTS):
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
        if idx < 0 or idx >= len(self.operands):
            raise IndexError("Operand out of range: " + str(idx))
        has_range_operands = any(isinstance(operand, ExprRange)
                                 for operand in self.operands)
        if len(self.operands) == 1 and not has_range_operands:
            with defaults.disabled_auto_reduction_types as disabled_types:
                disabled_types.add(And)
                return from_unary_and.instantiate({A: self.operands[0]},
                                                  assumptions=assumptions)
        if len(self.operands) == 2 and not has_range_operands:
            # Two operand special case:
            if idx == 0:
                return left_from_and.instantiate(
                    {A: self.operands[0], B: self.operands[1]},
                    assumptions=assumptions)
            elif idx == 1:
                return right_from_and.instantiate(
                    {A: self.operands[0], B: self.operands[1]},
                    assumptions=assumptions)
        else:
            # Multiple operands.
            from proveit.core_expr_types import Len
            operand_to_extract = self.operands[idx]
            if isinstance(operand_to_extract, ExprRange):
                # Derive the conjunction of a range of operands.
                return self.derive_some_from_and(idx, assumptions)
            else:
                A_sub = self.operands[:idx]
                B_sub = self.operands[idx]
                C_sub = self.operands[idx + 1:]
                m_val = Len(A_sub).computed(assumptions)
                n_val = Len(C_sub).computed(assumptions)
                return any_from_and.instantiate(
                    {m: m_val, n: n_val, A: A_sub, B: B_sub, C: C_sub},
                    assumptions=assumptions)

    def derive_some(self, start_idx, end_idx=None, assumptions=USE_DEFAULTS):
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
        l_val = Len(A_sub).computed(assumptions)
        m_val = Len(B_sub).computed(assumptions)
        n_val = Len(C_sub).computed(assumptions)
        return some_from_and.instantiate({l: l_val, m: m_val, n: n_val,
                                          A: A_sub, B: B_sub, C: C_sub},
                                         assumptions=assumptions)

    def derive_left(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land B)` derive :math:`A`.
        '''
        if len(self.operands) != 2:
            raise Exception(
                'derive_left only applicable for binary conjunction operations')
        return self.derive_any(0, assumptions)

    def derive_right(self, assumptions=USE_DEFAULTS):
        r'''
        From :math:`(A \land B)` derive :math:`B`.
        '''
        if len(self.operands) != 2:
            raise Exception(
                'derive_right only applicable for binary conjunction operations')
        return self.derive_any(1, assumptions)

    def unary_reduction(self, assumptions=USE_DEFAULTS):
        from proveit.logic.booleans.conjunction import \
            unary_and_reduction
        if not self.operands.is_singular():
            raise ValueError("Expression must have a single operand in "
                             "order to invoke unary_reduction")
        operand = self.operands[0]
        with defaults.disabled_auto_reduction_types as disable_reduction_types:
            disable_reduction_types.add(And)
            return unary_and_reduction.instantiate({A: operand},
                                                   assumptions=assumptions)

    def conclude_via_composition(self, assumptions=USE_DEFAULTS):
        '''
        Prove and return some (A and B ... and ... Z) via A, B, ..., Z each proven individually.
        See also the compose method to do this constructively.
        '''
        return compose(*self.operands, assumptions=assumptions)

    def deduce_left_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce A in Boolean from (A and B) in Boolean.
        '''
        from . import left_in_bool
        if len(self.operands) == 2:
            left_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def deduce_right_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce B in Boolean from (A and B) in Boolean.
        '''
        from . import right_in_bool
        if len(self.operands) == 2:
            right_in_bool.instantiate(
                {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)

    def deduce_parts_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Deduce A in Boolean, B in Boolean, ..., Z in Boolean
        from (A and B and ... and Z) in Boolean.
        '''
        for i in range(len(self.operands)):
            self.deduce_part_in_bool(i, assumptions)

    def deduce_part_in_bool(self, index_or_expr, assumptions=USE_DEFAULTS):
        '''
        Deduce X in Boolean from (A and B and .. and X and .. and Z) in Boolean
        provided X by expression or index number.
        '''
        from . import each_is_bool
        idx = index_or_expr if isinstance(
            index_or_expr, int) else list(
            self.operands).index(index_or_expr)
        if idx < 0 or idx >= len(self.operands):
            raise IndexError("Operand out of range: " + str(idx))
        if len(self.operands) == 2:
            if idx == 0:
                return self.deduce_left_in_bool(assumptions)
            elif idx == 1:
                return self.deduce_right_in_bool(assumptions)
        else:
            from proveit.numbers import num
            m_val, n_val = num(idx), num(len(self.operands) - idx - 1)
            return each_is_bool.instantiate({m: m_val,
                                             n: n_val,
                                             A: self.operands[:idx],
                                             B: self.operands[idx],
                                             C: self.operands[idx + 1:]},
                                            assumptions=assumptions)

    def conclude_via_demorgans(self, assumptions=USE_DEFAULTS):
        '''
        # created by JML 6/28/19
        From A and B and C conclude Not(Not(A) or Not(B) or Not(C))
        '''
        from . import demorgans_law_or_to_and, demorgans_law_or_to_and_bin
        from proveit.numbers import num
        if len(self.operands) == 2:
            return demorgans_law_or_to_and_bin.instantiate(
                {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        else:
            return demorgans_law_or_to_and.instantiate(
                {m: num(len(self.operands)), A: self.operands}, assumptions=assumptions)

    def conclude_via_example(self, true_operand, assumptions=USE_DEFAULTS):
        '''
        From one true operand, conclude that this 'or' expression is true.
        Requires all of the operands to be in the BOOLEAN set.
        '''
        from proveit.numbers import num
        from . import nand_if_not_one, nand_if_not_left, nand_if_not_right
        index = self.operands.index(true_operand)
        if len(self.operands) == 2:
            if index == 0:
                return nand_if_not_left.instantiate(
                    {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
            elif index == 1:
                return nand_if_not_right.instantiate(
                    {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        return nand_if_not_one.instantiate({m: num(index),
                                            n: num(len(self.operands) - index - 1),
                                            A: self.operands[:index],
                                            B: self.operands[index],
                                            C: self.operands[index + 1:]},
                                           assumptions=assumptions)

    def conclude_as_redundant(self, assumptions=USE_DEFAULTS):
        '''
        Conclude an expression of the form
        A and ..n repeats.. and A
        given n in Natural and A is TRUE.
        '''
        from proveit import ExprRange
        from proveit.numbers import one
        from . import redundant_conjunction
        if (len(self.operands) != 1 or
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
            {n: self.operands[0].end_index, A: _A}, assumptions=assumptions)

    def evaluation(self, assumptions=USE_DEFAULTS, *, automation=True,
                   minimal_automation=False, **kwargs):
        '''
        Attempt to determine whether this conjunction evaluates
        to true or false under the given assumptions.  If automation
        is False, it will only succeed if the evaluation is already
        known.  If automation and minimal_automation are True, it will
        only rely upon known  evaluations of the operands to determine
        whether to try to prove or disprove the conjunction.
        '''
        from proveit.logic import FALSE
        # load in truth-table evaluations
        from . import and_t_t, and_t_f, and_f_t, and_f_f
        if len(self.operands) == 0:
            return self.unary_reduction(assumptions)

        # First just see if it has a known evaluation.
        try:
            return Operation.evaluation(self, assumptions, automation=False)
        except SimplificationError as e:
            if not automation:
                raise e

        # Depending upon evaluations of operands, we will either
        # attempt to prove or disprove this conjunction.
        if minimal_automation:
            # Only do non-automated evaluations of operands
            # if minimal_automation is True.
            operand_automations = (False,)
        else:
            # First try non-automated operand evaluation, then
            # automated only if necessary.
            operand_automations = (False, True)
        for operand_automation in operand_automations:
            operands_evals = []
            for operand in self.operands:
                try:
                    operand_eval = operand.evaluation(
                        assumptions, automation=operand_automations)
                    operands_evals.append(operand_eval.rhs)
                except BaseException:
                    operands_evals.append(None)
            if FALSE in operands_evals:
                # If any operand is untrue, the conjunction may
                # only evaluate to false if it can be evaluated.
                self.disprove(assumptions)
                break
            elif None not in operands_evals:
                # If no operand is untrue and all the evaluations
                # are known, the conjunction may only evaluate
                # to true if it can be evaluated.
                self.prove(assumptions)
                break

        # If we had any success proving or disproving this conjunction
        # there should be a known evaluation now.
        return Operation.evaluation(self, assumptions, automation=False)

    def deduce_in_bool(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to deduce, then return, that this 'and' expression is in the BOOLEAN set.
        '''

        from . import binary_closure, closure
        if len(self.operands) == 2:
            return binary_closure.instantiate(
                {A: self.operands[0], B: self.operands[1]}, assumptions=assumptions)
        else:
            from proveit.numbers import num
        return closure.instantiate(
            {m: num(len(self.operands)), A: self.operands}, assumptions=assumptions)

    def commutation(
            self,
            init_idx=None,
            final_idx=None,
            assumptions=USE_DEFAULTS):
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
            rightward_commutation,
            assumptions)

    def group_commutation(
            self,
            init_idx,
            final_idx,
            length,
            disassociate=True,
            assumptions=USE_DEFAULTS):
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
            disassociate,
            assumptions)

    def commute(self, init_idx=None, final_idx=None, assumptions=USE_DEFAULTS):
        '''
        From self, derive and return a form in which the operand
        at index init_idx has been moved to final_idx.
        For example, given (A and B and ... and Y and Z) derive (A and ... and Y and B and Z)
        via init_idx = 1 and final_idx = -2.
        '''
        from . import commute, leftward_commute, rightward_commute
        return apply_commutation_thm(
            self,
            init_idx,
            final_idx,
            commute,
            leftward_commute,
            rightward_commute,
            assumptions)

    def group_commute(
            self,
            init_idx,
            final_idx,
            length,
            disassociate=True,
            assumptions=USE_DEFAULTS):
        '''
        Given self, deduce and return a form in which the operands
        at indices [init_idx, init_idx+length) have been moved to [final_idx. final_idx+length).
        It will do this by performing association first.  If disassocate is True, it
        will be disassociated afterwards.
        '''
        return group_commute(
            self,
            init_idx,
            final_idx,
            length,
            disassociate,
            assumptions)

    def association(self, start_idx, length, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (A and B and ... and Y and Z) = (A and B ... and (L and ... and M) and ... and Y and Z)
        '''
        from . import association
        return apply_association_thm(
            self, start_idx, length, association, assumptions)

    def associate(self, start_idx, length, assumptions=USE_DEFAULTS):
        '''
        From self, derive and return a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, from (A and B and ... and Y and Z) derive
        (A and B ... and (L and ... and M) and ... and Y and Z).
        '''
        from . import associate
        return apply_association_thm(
            self, start_idx, length, associate, assumptions)

    def disassociation(self, idx, assumptions=USE_DEFAULTS):
        '''
        Given Boolean operands, deduce that this expression is equal to a form in which the operand
        at index idx is no longer grouped together.
        For example, (A and B ... and (L and ... and M) and ... and Y and Z) = (A and B and ... and Y and Z)
        '''
        from . import disassociation
        return apply_disassociation_thm(self, idx, disassociation, assumptions)

    def disassociate(self, idx, assumptions=USE_DEFAULTS):
        '''
        From self, derive and return a form in which the operand
        at the given index is ungrouped.
        For example, from (A and B ... and (L and ... and M) and ... and Y and Z)
        derive (A and B and ... and Y and Z).
        '''
        from . import disassociate
        return apply_disassociation_thm(self, idx, disassociate, assumptions)


def compose(*expressions, assumptions=USE_DEFAULTS):
    '''
    Returns [A and B and ...], the And operator applied to the collection of given arguments,
    derived from each separately.
    '''
    if len(expressions) == 0:
        from proveit.logic.booleans.conjunction import \
            empty_conjunction
        return empty_conjunction
    if len(expressions) == 2:
        from . import and_if_both
        return and_if_both.instantiate(
            {A: expressions[0], B: expressions[1]}, assumptions=assumptions)
    else:
        from proveit.numbers import num
        from . import and_if_all
        return and_if_all.instantiate(
            {m: num(len(expressions)), A: expressions}, assumptions=assumptions)


# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(
    And, 'commutation', 'commuted', 'commute')
InnerExpr.register_equivalence_method(
    And,
    'group_commutation',
    'group_commuted',
    'group_commute')
InnerExpr.register_equivalence_method(
    And, 'association', 'associated', 'associate')
InnerExpr.register_equivalence_method(
    And, 'disassociation', 'disassociated', 'disassociate')
