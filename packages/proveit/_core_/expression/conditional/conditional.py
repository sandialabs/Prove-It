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

    def __init__(self, value, condition_or_conditions):
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

        Expression.__init__(self, ['Conditional'], (value, condition))

        self.value = value
        self.condition = condition

    @classmethod
    def _make(sub_class, core_info, sub_expressions):
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
        return Conditional(value, condition)

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

    def _formatted_condition(self, format_type, **kwargs):
        from proveit.logic import And
        if self.get_style('condition_delimiter') == 'comma':
            if (isinstance(self.condition, And)
                    and self.condition.operands.num_entries() > 1):
                return self.condition.operands.formatted(
                    format_type, fence=False, sub_fence=False,
                    operator_or_operators=', ', **kwargs)
        return self.condition.formatted(format_type)

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, fence=True, **kwargs):
        if format_type == "string":
            formatted_condition = self._formatted_condition('string', **kwargs)
            inner_str = self.value.formatted('string', **kwargs) + ' if ' + formatted_condition
            if fence:
                return '{' + inner_str + '.'
            return inner_str
        else:
            formatted_condition = self._formatted_condition('latex', **kwargs)
            inner_str = (self.value.formatted('latex', **kwargs) + r' \textrm{ if } '
                         + formatted_condition)
            if fence:
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

    def auto_reduction(self, assumptions=USE_DEFAULTS):
        '''
        Automatically reduce a conditional with a TRUE condition
        or with a condition that is a conjunction of two conjunctions,
        merging them into one.  This latter reduction is useful when
        merging conditions from two sources.  For example, showing\
        that
        \forall_{x | A, B} \forall_{y | C, D} P(x, y) =
           \forall_{x, y | A, B, C, D} P(x, y)
        would make use of this reduction.
        '''
        from proveit import a, m, n, Q, R
        from proveit.logic import And, TRUE
        if self.condition == TRUE:
            from proveit.core_expr_types.conditionals import \
                true_condition_reduction
            return true_condition_reduction.instantiate({a: self.value})
        elif (isinstance(self.value, Conditional) and
              self.condition == self.value.condition):
            from proveit.core_expr_types.conditionals import \
                redundant_condition_reduction
            return redundant_condition_reduction.instantiate(
                    {a: self.value.value, Q: self.condition},
                    assumptions = assumptions)            
        elif isinstance(self.condition, And):
            from proveit.core_expr_types.conditionals import \
                (singular_conjunction_condition_reduction,
                 condition_merger_reduction,
                 condition_append_reduction, condition_prepend_reduction,
                 condition_with_true_on_left_reduction,
                 condition_with_true_on_right_reduction)
            conditions = self.condition.operands
            if is_single(conditions):
                with defaults.disabled_auto_reduction_types as disabled_types:
                    # Don't auto-reduce 'And' in this process
                    disabled_types.discard(And)
                    return singular_conjunction_condition_reduction \
                        .instantiate({a: self.value, Q: conditions[0]})
            elif (conditions.num_entries() == 2 
                      and isinstance(conditions[0], And)):
                _Q = conditions[0].operands
                _m = _Q.num_elements(assumptions)
                return condition_append_reduction.instantiate(
                    {a: self.value, m: _m, Q: _Q, R: conditions[1]},
                    assumptions=assumptions)
            elif (conditions.num_entries() == 2 
                      and isinstance(conditions[1], And)):
                _R = conditions[1].operands
                _n = _R.num_elements(assumptions)
                return condition_prepend_reduction.instantiate(
                    {a: self.value, n: _n, Q: conditions[0], R: _R},
                    assumptions=assumptions)
            elif (conditions.num_entries() == 2 and
                    all(isinstance(cond, And) for cond in conditions)):
                _Q = conditions[0].operands
                _R = conditions[1].operands
                _m = _Q.num_elements(assumptions)
                _n = _R.num_elements(assumptions)
                _a = self.value
                return condition_merger_reduction.instantiate(
                    {m: _m, n: _n, a: _a, Q: _Q, R: _R},
                    assumptions=assumptions)
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
                _m = _Q.num_elements(assumptions)
                _a = self.value
                return thm.instantiate({m: _m, a: _a, Q: _Q},
                                       assumptions=assumptions)

    def _replaced(self, repl_map, allow_relabeling, reduction_map,
                  assumptions, requirements, equality_repl_requirements):
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
        subbed_cond = condition.replaced(
                repl_map, allow_relabeling, reduction_map,
                assumptions, requirements, equality_repl_requirements)

        # Next perform substitution on the value, adding the condition
        # as an assumption.
        subbed_val = value.replaced(
                repl_map, allow_relabeling, reduction_map,
                assumptions + (subbed_cond,), requirements,
                equality_repl_requirements)

        return Conditional(subbed_val, subbed_cond)
    
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
                    {a:equality.lhs, b:equality.rhs,
                     Q:self.condition}, assumptions = assumptions)
        elif equality.rhs == self.value:
            return conditional_substitution.instantiate(
                    {a:equality.rhs, b:equality.lhs,
                     Q:self.condition}, assumptions = assumptions)
        else:
            raise ValueError("One of the sides of %s was expected to "
                             "match the 'value' part of %s"
                             %(equality, self))
        