from proveit import (Function, Literal, USE_DEFAULTS, ProofFailure,
                     defaults, prover, relation_prover, equality_prover)
from proveit.logic.irreducible_value import IrreducibleValue
from proveit.logic.sets.membership import Membership, Nonmembership
from proveit import A, C, P, Q


class BooleanSet(Literal):
    def __init__(self, *, styles=None):
        Literal.__init__(
            self, string_format='BOOLEAN', latex_format=r'\mathbb{B}',
            styles=styles)

    def membership_object(self, element):
        return BooleanMembership(element)

    def nonmembership_object(self, element):
        return BooleanNonmembership(element)

    @prover
    def forall_evaluation(self, forall_stmt, **defaults_config):
        '''
        Given a forall statement over the BOOLEAN domain, evaluate to 
        TRUE or FALSE if possible.
        '''
        from proveit.logic import Forall, Equals, SimplificationError
        from . import false_eq_false, true_eq_true
        from . import forall_bool_eval_true, forall_bool_eval_false_via_t_f, \
            forall_bool_eval_false_via_f_f, forall_bool_eval_false_via_f_t
        from . import TRUE, FALSE, Boolean
        from .conjunction import compose
        assert(isinstance(forall_stmt, Forall)
               ), "May only apply forall_evaluation method of BOOLEAN to a forall statement"
        assert(forall_stmt.domain ==
               Boolean), "May only apply forall_evaluation method of BOOLEAN to a forall " \
                         "statement with the BOOLEAN domain"
        with defaults.temporary() as temp_defaults:
            temp_defaults.preserved_exprs = defaults.preserved_exprs.union([forall_stmt.inner_expr])
            instance_list = list(forall_stmt.instance_param_lists())
            instance_var = instance_list[0][0]
            instance_expr = forall_stmt.instance_expr
            P_op = Function(P, instance_var)
            true_instance = instance_expr.basic_replaced(
                    {instance_var: TRUE})
            false_instance = instance_expr.basic_replaced(
                    {instance_var: FALSE})
            temp_defaults.auto_simplify = False
            if true_instance == TRUE and false_instance == FALSE:
                # special case of Forall_{A in BOOLEAN} A
                false_eq_false  # FALSE = FALSE
                true_eq_true  # TRUE = TRUE
                return forall_bool_eval_false_via_t_f.instantiate(
                    {P_op: instance_expr}).derive_conclusion()
            else:
                # must evaluate for the TRUE and FALSE case separately
                eval_true_instance = true_instance.evaluation()
                eval_false_instance = false_instance.evaluation()
                if not isinstance(
                        eval_true_instance.expr,
                        Equals) or not isinstance(
                        eval_false_instance.expr,
                        Equals):
                    raise SimplificationError(
                        'Quantified instances must produce equalities as '
                        'evaluations')
                # proper evaluations for both cases (TRUE and FALSE)
                true_case_val = eval_true_instance.rhs
                false_case_val = eval_false_instance.rhs
                if true_case_val == TRUE and false_case_val == TRUE:
                    # both cases are TRUE, so the forall over the
                    # boolean set is TRUE
                    compose([eval_true_instance.derive_via_boolean_equality(), 
                             eval_false_instance.derive_via_boolean_equality()])
                    return forall_bool_eval_true.instantiate(
                            {P_op: instance_expr, A: instance_var})
                else:
                    # one case is FALSE, so the forall over the boolean set is
                    # FALSE
                    compose([eval_true_instance, eval_false_instance])
                    if true_case_val == FALSE and false_case_val == FALSE:
                        impl = forall_bool_eval_false_via_f_f.instantiate(
                            {P_op: instance_expr, A: instance_var})
                    elif true_case_val == FALSE and false_case_val == TRUE:
                        impl = forall_bool_eval_false_via_f_t.instantiate(
                            {P_op: instance_expr, A: instance_var})
                    elif true_case_val == TRUE and false_case_val == FALSE:
                        impl = forall_bool_eval_false_via_t_f.instantiate(
                            {P_op: instance_expr, A: instance_var})
                    else:
                        raise SimplificationError(
                            'Quantified instance evaluations must be TRUE or FALSE')
                    return impl.derive_conclusion()

    @prover
    def unfold_forall(self, forall_stmt, **defaults_config):
        '''
        Given forall_{A in Boolean} P(A), derive and return [P(TRUE) and P(FALSE)].
        '''
        from proveit.logic import Forall
        from . import unfold_forall_over_bool
        from . import Boolean
        assert(isinstance(forall_stmt, Forall)
               ), "May only apply unfold_forall method of Boolean to a forall statement"
        assert(forall_stmt.domain ==
               Boolean), "May only apply unfold_forall method of Boolean to a forall statement with the Boolean domain"
        Px = Function(P, forall_stmt.instance_var)
        _Px = forall_stmt.instance_expr
        _A = forall_stmt.instance_var
        return unfold_forall_over_bool.instantiate(
            {Px: _Px, A: _A}).derive_consequent()

    @prover
    def fold_as_forall(self, forall_stmt, **defaults_config):
        '''
        Given forall_{A in Boolean} P(A), conclude and return it from
        [P(TRUE) and P(FALSE)].
        '''
        from proveit.logic import Forall, And
        from . import fold_forall_over_bool, fold_conditioned_forall_over_bool
        from . import Boolean
        assert(isinstance(forall_stmt, Forall)
               ), "May only apply fold_as_forall method of Boolean to a forall statement"
        assert(forall_stmt.domain ==
               Boolean), "May only apply fold_as_forall method of Boolean to a forall statement with the Boolean domain"
        if forall_stmt.conditions.num_entries() > 1:
            if forall_stmt.conditions.is_double():
                condition = forall_stmt.conditions[1]
            else:
                condition = And(*forall_stmt.conditions[1:].entries)
            Qx = Function(Q, forall_stmt.instance_param)
            _Qx = condition
            Px = Function(P, forall_stmt.instance_param)
            _Px = forall_stmt.instance_expr
            _A = forall_stmt.instance_param
            return fold_conditioned_forall_over_bool.instantiate(
                {Qx: _Qx, Px: _Px, A: _A}, num_forall_eliminations=1, preserve_expr=forall_stmt)
        else:
            # forall_{A in Boolean} P(A), assuming P(TRUE) and P(FALSE)
            Px = Function(P, forall_stmt.instance_param)
            _Px = forall_stmt.instance_expr
            _A = forall_stmt.instance_param
            return fold_forall_over_bool.instantiate(
                {Px: _Px, A: _A}, num_forall_eliminations=1)


class BooleanMembership(Membership):
    '''
    Defines methods that apply to InSet(element, Boolean) objects
    via InSet.__getattr__ which calls Boolean.membership_object(element)
    to return a BooleanMembership object.
    '''

    def __init__(self, element):
        from . import Boolean
        Membership.__init__(self, element, Boolean)

    def side_effects(self, judgment):
        '''
        Yield side-effect methods to try when the element is proven to be in the Boolean set
        by calling 'in_bool_side_effects' on the element if it has such a method.
        Edited by JML on 6/27/19 to add fold_is_bool side_effect
        '''
        from proveit.logic.booleans import unfold_is_bool, fold_is_bool
        if hasattr(self.element, 'in_bool_side_effects'):
            for side_effect in self.element.in_bool_side_effects(judgment):
                yield side_effect
        # don't automatically do unfold_is_bool_explicit if unfold_is_bool is
        # unusable -- avoids infinite recursion
        if unfold_is_bool.is_usable():
            yield self.unfold

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to deduce that the given element is in the Boolean set under the given assumptions.
        '''
        from . import in_bool_if_true, in_bool_if_false
        element = self.element
        # if the element is already proven or disproven, use in_bool_if_true or
        # in_bool_if_false
        try:
            element.prove(automation=False)
            return in_bool_if_true.instantiate({A: element})
        except ProofFailure:
            pass
        try:
            element.disprove(automation=False)
            return in_bool_if_false.instantiate({A: element})
        except ProofFailure:
            pass
        # Use 'deduce_in_bool' if the element has that method.
        if hasattr(element, 'deduce_in_bool'):
            return element.deduce_in_bool()
        raise ProofFailure(in_bool(element), defaults.assumptions, str(
            element) + ' not proven to be equal to TRUE or FALSE.')

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Deduce [(element in Boolean) = 
                [(element = TRUE) or (element = FALSE)].
        '''
        from . import in_bool_def
        return in_bool_def.instantiate({A: self.element})

    @prover
    def unfold(self, **defaults_config):
        '''
        From in_bool(Element), derive and return [element or not(element)] if
        unfold_is_bool is usable.  It it is not, instead try to derive and return
        [(element=TRUE) or (element=FALSE)].
        '''
        from . import unfold_is_bool, unfold_is_bool_explicit
        if unfold_is_bool.is_usable():
            #  [element or not(element)] assuming in_bool(element)
            return unfold_is_bool.instantiate(
                {A: self.element})
        else:
            #  [(element = TRUE) or (element = FALSE)] assuming in_bool(element)
            return unfold_is_bool_explicit.instantiate(
                {A: self.element})

    @prover
    def fold(self, **defaults_config):
        '''
        From [(element=TRUE) or (element=FALSE)], derive in_bool(Element).
        Created by JML on 6/27/19 for fold_is_bool side_effect
        '''
        from . import fold_is_bool
        if fold_is_bool.is_usable():
            return fold_is_bool.instantiate(
                {A: self.element}, preserve_expr=in_bool(self.element))

    @prover
    def derive_via_excluded_middle(self, consequent, **defaults_config):
        '''
        Derive the consequent from (element in Boolean)
        given element => consequent and Not(element) => consequent.
        '''
        from . import from_excluded_middle
        return from_excluded_middle.instantiate(
            {A: self.element, C: consequent}, preserve_expr=consequent)

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import in_bool_is_bool
        return in_bool_is_bool.instantiate({A: self.element})


class BooleanNonmembership(Nonmembership):

    def __init__(self, element):
        Nonmembership.__init__(self)

    @equality_prover("defined", "define")
    def definition(self, element, **defaults_config):
        '''
        Derive [(element not in Boolean) = [(element != TRUE) and (element != FALSE)].
        '''
        from . import not_in_bool_equiv
        return not_in_bool_equiv.instantiate({A: element})


class TrueLiteral(Literal, IrreducibleValue):
    def __init__(self, *, styles=None):
        Literal.__init__(self, string_format='TRUE', latex_format=r'\top',
                         styles=styles)

    @prover
    def conclude(self, **defaults_config):
        from . import true_axiom
        return true_axiom

    @prover
    def eval_equality(self, other, **defaults_config):
        from . import true_eq_true, true_not_false
        from . import TRUE, FALSE
        if other == TRUE:
            return true_eq_true.evaluation()
        elif other == FALSE:
            return true_not_false.unfold().equate_negated_to_false()

    @relation_prover
    def not_equal(self, other, **defaults_config):
        from . import true_not_false
        from . import TRUE, FALSE
        if other == FALSE:
            return true_not_false
        if other == TRUE:
            raise ProofFailure(
                "Cannot prove TRUE != TRUE since that statement is false")
        raise ProofFailure(
            "Inequality between TRUE and a non-boolean not defined")

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import true_is_bool
        return true_is_bool


class FalseLiteral(Literal, IrreducibleValue):
    def __init__(self, *, styles=None):
        Literal.__init__(self, string_format='FALSE', latex_format=r'\bot',
                         styles=styles)

    @prover
    def eval_equality(self, other, **defaults_config):
        from . import false_not_true
        from . import false_eq_false
        from . import TRUE, FALSE
        if other == FALSE:
            return false_eq_false.evaluation()
        elif other == TRUE:
            return false_not_true.unfold().equate_negated_to_false()

    @prover
    def conclude_negation(self, **defaults_config):
        from proveit.logic.booleans.negation import not_false
        return not_false  # the negation of FALSE

    @relation_prover
    def not_equal(self, other, **defaults_config):
        from _.theorems_ import false_not_true
        from . import TRUE, FALSE
        if other == TRUE:
            return false_not_true
        if other == FALSE:
            raise ProofFailure(
                "Cannot prove FALSE != FALSE since that statement is false")
        raise ProofFailure(
            "Inequality between FALSE and a non-boolean not defined")

    @prover
    def deduce_in_bool(self, **defaults_config):
        from . import false_is_bool
        return false_is_bool

    @prover
    def deny_assumption(self, assumption_to_deny, **defaults_config):
        '''
        If FALSE can be proven under a set of assumptions, any one
        of those assumptions may be proven untrue given the other
        assumptions.
        '''
        impl = self.prove(assumptions).as_implication(assumption_to_deny)
        return impl.deny_antecedent()


def in_bool(*elements):
    from proveit.logic.sets import InSet
    from . import Boolean
    if len(elements) == 1:
        return InSet(elements[0], Boolean)
    return [InSet(element, Boolean) for element in elements]
