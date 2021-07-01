from proveit.decorators import prover, equality_prover
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.composite import is_single
from proveit._core_.defaults import defaults, USE_DEFAULTS

class Conditional(Expression):
    '''
    A Conditional expression is one that may reduce to its 'value'
    if and only if its 'condition' evaluates to TRUE.  The value
    is only relevant when the condition is TRUE and therefore the
    value may be replaced with an equivalent expression under the
    assumption that the condition is TRUE.  When the condition is
    not TRUE, there is no defined reduction of the Conditional.  All
    such irreducible Conditionals are regarded to be equivalent.
    Thus, two Lambda expressions with the same number of parameters
    and having Conditional bodies with the same conditions are regarded
    to be equivalent if their respective Conditional values are equal
    in all instances for which the condition is satisfied.  Also, for
    an OperationOverInstances having a lambda map with a Conditional
    body, only the instances in which the condition is TRUE are valid
    instances and the rest are disregarded.
    '''

    def __init__(self, value, condition_or_conditions, *, styles=None):
        '''
        Create a Conditional with the given particular value
        and the given condition.  If multiple conditions are
        provided, these will be wrapped in a conjunction internally.
        However, if the 'condition_delimiter' style is set to 'comma', 
        the conditions will be displayed in a comma
        delimited fashion if it is within a conjunction.
        '''
        from proveit._core_.expression.composite import \
            single_or_composite_expression, Composite, ExprTuple, ExprRange

        value = single_or_composite_expression(value)
        assert (isinstance(value, Expression)
                and not isinstance(value, ExprRange))

        condition_or_conditions = \
            single_or_composite_expression(condition_or_conditions)

        if isinstance(condition_or_conditions, ExprTuple):
            if is_single(condition_or_conditions):
                condition = condition_or_conditions[0]
            else:
                # Must wrap a tuple of conditions in a conjunction.
                from proveit.logic import And
                condition = And(*condition_or_conditions.entries)
        else:
            condition = condition_or_conditions
        assert (isinstance(condition, Expression) and
                not isinstance(condition, Composite))

        Expression.__init__(self, ['Conditional'], (value, condition),
                            styles=styles)

        self.value = value
        self.condition = condition

    @classmethod
    def _make(sub_class, core_info, sub_expressions, *, styles):
        if len(core_info) != 1 or core_info[0] != 'Conditional':
            raise ValueError(
                "Expecting Conditional core_info to contain exactly "
                ":one item: 'Conditional'")
        if sub_class != Conditional:
            raise MakeNotImplemented(sub_class)
        if len(sub_expressions) != 2:
            raise ValueError(
                "Expecting Conditional to have two sub-expressions.")
        value, condition = sub_expressions
        return Conditional(value, condition, styles=styles)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Indexed.
        '''
        yield self.value
        yield self.condition

    def style_options(self):
        '''
        Return the StyleOptions for this Conditional.
        '''
        from proveit import StyleOptions
        options = StyleOptions(self)
        options.add_option(
                name = 'condition_delimiter', 
                description = ("'comma' or 'and'"),
                default = 'comma',
                related_methods = ('with_comma_delimiter',
                                   'with_conjunction_delimiter')
                )
        return options
    
    def with_comma_delimiter(self):
        return self.with_styles(condition_delimiter='comma')
    
    def with_conjunction_delimiter(self):
        return self.with_styles(condition_delimiter='and')

    def _formatted_condition(self, format_type):
        from proveit.logic import And
        if self.get_style('condition_delimiter') == 'comma':
            if (isinstance(self.condition, And)
                    and self.condition.operands.num_entries() > 1):
                return self.condition.operands.formatted(
                    format_type, fence=False, sub_fence=False,
                    operator_or_operators=', ')
        return self.condition.formatted(format_type)

    def string(self, **kwargs):
        formatted_condition = self._formatted_condition('string')
        inner_str = self.value.string() + ' if ' + formatted_condition
        if kwargs.get('fence', True):
            return '{' + inner_str + '.'
        return inner_str

    def latex(self, **kwargs):
        formatted_condition = self._formatted_condition('latex')
        inner_str = (self.value.latex() + r' \textrm{ if } '
                     + formatted_condition)
        if kwargs.get('fence', True):
            inner_str = r'\left\{' + inner_str + r'\right..'
        return inner_str

    '''
    def do_reduced_evaluation(self, assumptions=USE_DEFAULTS, **kwargs):
        from proveit.logic import EvaluationError, TRUE
        for condition in self.conditions:
            if condition == TRUE:
                return value # ACTUALLY, THIS MUST BE PROVED
        raise EvaluationError(self, assumptions)
    '''


    @equality_prover('simplified', 'simplify')
    def simplification(self, **defaults_config):
        from proveit.relation import TransRelUpdater
        from proveit.logic import And
        
        expr = self
        eq = TransRelUpdater(expr)
        if True:#not self.value.is_simplified():
            # Simplify the 'value'.
            expr = eq.update(
                    expr.value_substitution(self.value.simplification()))
        if isinstance(self.condition, And):
            # Simplify the conditions.
            if True:#any(not condition.is_simplified() for condition 
               #    in self.condition.operands.entries):
                inner_condition = expr.inner_expr().condition
                expr = eq.update(inner_condition.simplification_of_operands())
        elif True:#not self.condition.is_simplified():
            # Simplify the condition.
            expr = eq.update(
                    expr.condition_substitution(
                            self.condition.simplification()))
        # Perform a shallow simplifation on this Conditional.
        eq.update(expr.shallow_simplification())
        
        return eq.relation

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Handles various Conditional reductions:
            {a if T.  =  a
            {{a if Q. if Q.  =  {a if Q.
            {a if [⋀](Q).  =  {a if Q.
            {a if a ⋀ b, c ⋀ d.  =  {a if a ⋀ b ⋀ c ⋀ d.
            etc.
        '''
        from proveit import a, m, n, Q, R
        from proveit.logic import And, TRUE, Equals
        if self.condition == TRUE:
            from proveit.core_expr_types.conditionals import \
                true_condition_reduction
            return true_condition_reduction.instantiate({a: self.value})
        elif (isinstance(self.value, Conditional) and
              self.condition == self.value.condition):
            from proveit.core_expr_types.conditionals import \
                redundant_condition_reduction
            return redundant_condition_reduction.instantiate(
                    {a: self.value.value, Q: self.condition})            
        elif isinstance(self.condition, And):
            from proveit.core_expr_types.conditionals import \
                (singular_conjunction_condition_reduction,
                 condition_merger_reduction,
                 condition_append_reduction, condition_prepend_reduction,
                 condition_with_true_on_left_reduction,
                 condition_with_true_on_right_reduction)
            conditions = self.condition.operands
            if is_single(conditions):
                return singular_conjunction_condition_reduction \
                    .instantiate({a: self.value, Q: conditions[0]})
            elif (conditions.is_double() and
                    all(isinstance(cond, And) for cond in conditions)):
                _Q = conditions[0].operands
                _R = conditions[1].operands
                _m = _Q.num_elements()
                _n = _R.num_elements()
                _a = self.value
                return condition_merger_reduction.instantiate(
                    {m: _m, n: _n, a: _a, Q: _Q, R: _R})
            elif (conditions.num_entries() == 2 and
                    any(isinstance(cond, And) for cond in conditions) and
                    any(cond == TRUE for cond in conditions)):
                if conditions[0] == TRUE:
                    thm = condition_with_true_on_left_reduction
                    _Q = conditions[1].operands
                else:
                    assert conditions[1] == TRUE
                    thm = condition_with_true_on_right_reduction
                    _Q = conditions[0].operands
                _m = _Q.num_elements()
                _a = self.value
                return thm.instantiate({m: _m, a: _a, Q: _Q})
            elif (conditions.is_double() 
                      and isinstance(conditions[0], And)):
                _Q = conditions[0].operands
                _m = _Q.num_elements()
                return condition_append_reduction.instantiate(
                    {a: self.value, m: _m, Q: _Q, R: conditions[1]})
            elif (conditions.is_double()
                      and isinstance(conditions[1], And)):
                _R = conditions[1].operands
                _n = _R.num_elements()
                return condition_prepend_reduction.instantiate(
                    {a: self.value, n: _n, Q: conditions[0], R: _R})
        # Use trivial self-reflection if there is no other 
        # simplification to do.
        return Equals(self, self).prove()

    def basic_replaced(self, repl_map, *,
                       allow_relabeling=False, requirements=None):
        '''
        Returns this expression with sub-expressions replaced
        according to the replacement map (repl_map) dictionary.

        'assumptions' and 'requirements' are used when an operator is
        replaced by a Lambda map that has iterated parameters such that
        the length of the parameters and operands must be proven to be equal.
        For more details, see Operation.replaced, Lambda.apply, and
        ExprRange.replaced (which is the sequence of calls involved).

        For a Conditional, the 'condition' is added to the assumptions
        when 'replaced' is called on the 'value'.
        '''
        if len(repl_map) > 0 and (self in repl_map):
            # The full expression is to be replaced.
            return repl_map[self]

        value = self.value
        condition = self.condition

        # First perform substitution on the conditions:
        subbed_cond = condition.basic_replaced(
                repl_map, allow_relabeling=allow_relabeling,
                requirements=requirements)

        # Next perform substitution on the value, adding the condition
        # as an assumption.
        with defaults.temporary() as temp_defaults:
            temp_defaults.assumptions = defaults.assumptions + (subbed_cond,)
            subbed_val = value.basic_replaced(
                    repl_map, allow_relabeling=allow_relabeling,
                    requirements=requirements)

        return Conditional(subbed_val, subbed_cond,
                           styles=self._style_data.styles)

    def _auto_simplified_sub_exprs(self, *, requirements, stored_replacements):
        '''
        Properly handle the Conditional scope while doing 
        auto-simplification replacements.
        '''
        subbed_cond = self.condition._auto_simplified(
                requirements=requirements, 
                stored_replacements=stored_replacements)
        # Add the 'condition' as an assumption for the 'value' scope.
        with defaults.temporary() as temp_defaults:
            prev_num_assumptions = len(defaults.assumptions)
            temp_defaults.assumptions = (
                    defaults.assumptions + (subbed_cond,))
            if len(defaults.assumptions) > prev_num_assumptions:
                # Since the assumptions have changed, we can no longer
                # use the stored_replacements from before.
                stored_replacements = dict()
            subbed_val = self.value._auto_simplified(
                    requirements=requirements,
                    stored_replacements=stored_replacements)
        if (subbed_val._style_id == self.value._style_id and
                subbed_cond._style_id == self.condition._style_id):
            # Nothing change, so don't remake anything.
            return self
        return Conditional(subbed_val, subbed_cond,
                           styles=self._style_data.styles)
    
    def value_substitution(self, equality, assumptions=USE_DEFAULTS):
        '''
        Equate this Conditional to one that has the value
        substituted.  For example,
        {a if Q. = {b if Q.
        given the "a = b" equality under the assumption of Q.
        The 'equality' may be universally quantified.
        '''
        from proveit import (Lambda, ArgumentExtractionError,
                             Judgment)
        from proveit import a, b, Q
        from proveit.logic import Equals, Forall
        from proveit.core_expr_types.conditionals import (
                conditional_substitution)
        assumptions = defaults.checked_assumptions(assumptions)
        def raise_type_error():
            raise TypeError("'equality' expected to be of type Equals "
                            "or a universally quantified equality, "
                            "got %s of type %s instead."
                            %(equality, equality.__class__))            
        if isinstance(equality, Judgment):
            equality = equality.expr
        if isinstance(equality, Forall):
            quantified_eq = equality
            def raise_invalid_condition_error():
                raise ValueError("Condition of universally quantified "
                                 "equality, %s, expected to match %s."
                                 %(quantified_eq, self.condition))      
            equality = quantified_eq.instance_expr
            if not isinstance(equality, Equals):
                raise_type_error()
            if not hasattr(quantified_eq, 'condition'):
                raise_invalid_condition_error()
            condition = quantified_eq.condition
            _y = quantified_eq.instance_params
            _Q = Lambda(_y, condition)
            try:
                _x = _Q.extract_arguments(self.condition)
            except ArgumentExtractionError:
                raise_invalid_condition_error()
            equality = quantified_eq.instantiate(
                    {_y:_x}, assumptions = assumptions + (condition,))
            return self.value_substitution(equality, assumptions)
        if not isinstance(equality, Equals):
            raise_type_error()
        if equality.lhs == self.value:
            return conditional_substitution.instantiate(
                    {a:equality.lhs, b:equality.rhs, Q:self.condition}, 
                    assumptions = assumptions)
        elif equality.rhs == self.value:
            return conditional_substitution.instantiate(
                    {a:equality.rhs, b:equality.lhs, Q:self.condition}, 
                    assumptions = assumptions)
        else:
            raise ValueError("One of the sides of %s was expected to "
                             "match the 'value' part of %s"
                             %(equality, self))

    def condition_substitution(self, equality, assumptions=USE_DEFAULTS):
        '''
        Equate this Conditional to one that has the condition
        substituted.  For example,
        {a if Q. = {a if R.
        given "Q = R".
        '''
        from proveit import a, Q, R
        from proveit.core_expr_types.conditionals import (
                condition_substitution)
        if equality.lhs == self.condition:
            return condition_substitution.instantiate(
                    {a:self.value, Q:equality.lhs, R:equality.rhs})
        elif equality.rhs == self.condition:
            return condition_substitution.instantiate(
                    {a:self.value, Q:equality.rhs, R:equality.lhs})
        else:
            raise ValueError("%s is not an appropriate 'equality' for "
                             "condition_substitution on %s (the 'condition' "
                             "is not matched on either side)"
                             %(equality, self))