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
        with defaults.temporary() as temp_defaults:
            # Add the condition as an assumption when formatting the
            # value.
            temp_defaults.automation = False
            temp_defaults.assumptions = defaults.assumptions + (self.condition,)
            formatted_value = self.value.formatted(format_type, **kwargs)
        if format_type == "string":
            formatted_condition = self._formatted_condition('string', **kwargs)
            inner_str = formatted_value + ' if ' + formatted_condition
            if fence:
                return '{' + inner_str + '.'
            return inner_str
        else:
            formatted_condition = self._formatted_condition('latex', **kwargs)
            inner_str = (formatted_value + r' \textrm{ if } '
                         + formatted_condition)
            if fence:
                inner_str = r'\left\{' + inner_str + r'\right..'
            return inner_str

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

    def _auto_simplified_sub_exprs(self, *, requirements, stored_replacements,
                                   markers_and_marked_expr):
        '''
        Properly handle the Conditional scope while doing 
        auto-simplification replacements.
        '''
        recursion_fn = lambda expr, requirements, stored_repls, sub_expr_fn : (
                     expr._auto_simplified(
                        requirements=requirements, 
                        stored_replacements=stored_repls,
                        markers_and_marked_expr=self._update_marked_expr(
                                markers_and_marked_expr, sub_expr_fn)))
        subbed_val, subbed_cond = self._equality_replaced_sub_exprs(
                recursion_fn, requirements=requirements,
                stored_replacements=stored_replacements)
        if (subbed_val._style_id == self.value._style_id and
                subbed_cond._style_id == self.condition._style_id):
            # Nothing change, so don't remake anything.
            return self
        return Conditional(subbed_val, subbed_cond,
                           styles=self._style_data.styles)        

    def _equality_replaced_sub_exprs(self, recursion_fn, *, requirements, 
                                     stored_replacements):
        '''
        Helper for Conditional._auto_simplified_sub_exprs and
        Expression._manual_equality_replaced.  The 'recursion_fn'
        allows this to satisfy both roles.
        '''
        from proveit.logic import And
        # Add the 'condition' as an assumption for the 'value' scope.
        # If there are multiple conditions in a conjunction, add them
        # as assumptions one by one and allow them to be used for
        # subsequent conditions.
        if isinstance(self.condition, And):
            conditions = self.condition.operands.entries
        else:
            conditions = [self.condition]
        build_get_cond_fn = lambda _k : (lambda _expr : 
                                         _expr.condition.operands[_k] if isinstance(_expr.condition, And)
                                         else _expr.condition)
        
        # For each condition, we'll assume the previous substituted
        # conditions.
        subbed_conds = []
        prev_assumptions = defaults.assumptions
        inner_stored_repls = stored_replacements
        for _k, cond in enumerate(conditions):
            inner_assumptions = (defaults.assumptions 
                                 + tuple(subbed_conds))
            with defaults.temporary() as temp_defaults:
                temp_defaults.assumptions = inner_assumptions
                if defaults.assumptions != prev_assumptions:
                    # Since the assumptions have changed, we can no 
                    # longer use the stored_replacements from before.
                    inner_stored_repls = dict()
                prev_assumptions = defaults.assumptions
                subbed_conds.append(
                        recursion_fn(cond, requirements, inner_stored_repls,
                                     build_get_cond_fn(_k)))
    
        # For the value, we'll assume all of the substituted conditions.
        inner_assumptions = (defaults.assumptions  + tuple(subbed_conds))
        with defaults.temporary() as temp_defaults:
            temp_defaults.assumptions = inner_assumptions
            if defaults.assumptions != prev_assumptions:
                # Since the assumptions have changed, we can no longer
                # use the stored_replacements from before.
                inner_stored_repls = dict()
            subbed_val = recursion_fn(self.value,
                    requirements, inner_stored_repls, 
                    lambda _expr : _expr.value)
        if len(subbed_conds) == 1:
            return (subbed_val, subbed_conds[0])
        else:
            subbed_condition = And(*subbed_conds)
            if subbed_condition != self.condition:
                # We can replace the altered subbed condition
                # conjunction; use the original assumptions and
                # stored replacements.
                subbed_condition = recursion_fn(
                        subbed_condition, requirements, stored_replacements, 
                        lambda _expr : _expr.condition)
            return (subbed_val, subbed_condition)

    @equality_prover('simplified', 'simplify')
    def simplification(self, **defaults_config):
        from proveit.relation import TransRelUpdater
        from proveit.logic import And
        
        expr = self
        eq = TransRelUpdater(expr)
        if True:#not self.value.is_simplified():
            # Simplify the 'value'.
            expr = eq.update(
                    expr.value_substitution(self.value.simplification(
                            assumptions=defaults.assumptions+(
                                    self.condition,))))
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
        # If the expression has not been reduced yet, no need for an
        # "evaluation check" by the @prover decorator.
        _no_eval_check = (expr == self)
        eq.update(expr.shallow_simplification(_no_eval_check=_no_eval_check))
        
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
        elif self.condition.proven():
            return self.satisfied_condition_reduction()
        elif self.condition.disproven():
            return self.dissatisfied_condition_reduction()
        elif (isinstance(self.value, Conditional) and
              self.condition == self.value.condition):
            from proveit.core_expr_types.conditionals import \
                redundant_condition_reduction
            return redundant_condition_reduction.instantiate(
                    {a: self.value.value, Q: self.condition})            
        elif isinstance(self.condition, And):
            conditions = self.condition.operands
            if is_single(conditions):
                from proveit.core_expr_types.conditionals import (
                        singular_conjunction_condition_reduction)
                return singular_conjunction_condition_reduction \
                    .instantiate({a: self.value, Q: conditions[0]})
            elif (conditions.is_double() and
                    all(isinstance(cond, And) for cond in conditions)):
                from proveit.core_expr_types.conditionals import (
                        condition_merger_reduction)                
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
                from proveit.core_expr_types.conditionals import (
                        condition_with_true_on_left_reduction,
                        condition_with_true_on_right_reduction)
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
                from proveit.core_expr_types.conditionals import (
                        condition_append_reduction)                
                _Q = conditions[0].operands
                _m = _Q.num_elements()
                return condition_append_reduction.instantiate(
                    {a: self.value, m: _m, Q: _Q, R: conditions[1]})
            elif (conditions.is_double()
                      and isinstance(conditions[1], And)):
                from proveit.core_expr_types.conditionals import (
                        condition_prepend_reduction)                
                _R = conditions[1].operands
                _n = _R.num_elements()
                return condition_prepend_reduction.instantiate(
                    {a: self.value, n: _n, Q: conditions[0], R: _R})
            elif any(cond==TRUE for cond in conditions):
                from proveit.core_expr_types.conditionals import (
                        true_condition_elimination)                
                idx = conditions.index(TRUE)
                _Q = conditions[:idx]
                _R = conditions[idx+1:]
                _m = _Q.num_elements()
                _n = _R.num_elements()
                return true_condition_elimination.instantiate(
                        {a:self.value, Q:_Q, R:_R, m:_m, n:_n})
        elif must_evaluate:
            # The only way we can equate a Conditional to an
            # irreducible is if we prove the condition to be true.
            self.condition.prove()
            return self.evaluation()
        # Use trivial self-reflection if there is no other 
        # simplification to do.
        return Equals(self, self).prove()
    
    @equality_prover('satisfied_condition_reduced', 
                     'satisfied_condition_reduce')
    def satisfied_condition_reduction(self, **defaults_config):
        from proveit import a, Q
        from proveit.core_expr_types.conditionals import \
            satisfied_condition_reduction
        return satisfied_condition_reduction.instantiate(
                {a: self.value, Q: self.condition})

    @equality_prover('dissatisfied_condition_reduced', 
                     'dissatisfied_condition_reduce')
    def dissatisfied_condition_reduction(self, **defaults_config):
        from proveit import a, Q
        from proveit.core_expr_types.conditionals import \
            dissatisfied_condition_reduction
        return dissatisfied_condition_reduction.instantiate(
                {a: self.value, Q: self.condition})

    @equality_prover('value_substituted', 
                     'value_substitute')
    def value_substitution(self, equality, **defaults_config):
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
                    {_y:_x}, assumptions = defaults.assumptions + (condition,))
            return self.value_substitution(equality)
        if not isinstance(equality, Equals):
            raise_type_error()
        if equality.lhs == self.value:
            return conditional_substitution.instantiate(
                    {a:equality.lhs, b:equality.rhs, Q:self.condition})
        elif equality.rhs == self.value:
            return conditional_substitution.instantiate(
                    {a:equality.rhs, b:equality.lhs, Q:self.condition})
        else:
            raise ValueError("One of the sides of %s was expected to "
                             "match the 'value' part of %s"
                             %(equality, self))

    @equality_prover('condition_substituted', 
                     'substitute_condition')
    def condition_substitution(self, condition_equivalence_or_equality, 
                               **defaults_config):
        '''
        Equate this Conditional to one that has the condition
        substituted.  For example,
        {a if Q. = {a if R.
        given "Q ⟺ R".
        '''
        from proveit import Judgment
        from proveit import a, Q, R
        from proveit.core_expr_types.conditionals import (
                condition_replacement, condition_substitution)
        from proveit.logic import Iff, Equals
        if isinstance(condition_equivalence_or_equality, Judgment):
            condition_equivalence_or_equality = (
                condition_equivalence_or_equality.expr)
        if isinstance(condition_equivalence_or_equality, Iff):
            equivalence = condition_equivalence_or_equality
            if equivalence.lhs == self.condition:
                return condition_replacement.instantiate(
                    {a:self.value, Q:equivalence.lhs, 
                     R:equivalence.rhs})
            elif equivalence.rhs == self.condition:
                return condition_replacement.instantiate(
                    {a:self.value, Q:equivalence.rhs, 
                     R:equivalence.lhs})
        elif isinstance(condition_equivalence_or_equality, Equals):
            equality = condition_equivalence_or_equality
            if equality.lhs == self.condition:
                return condition_substitution.instantiate(
                    {a:self.value, Q:equality.lhs, 
                     R:equality.rhs})
            elif equality.rhs == self.condition:
                return condition_substitution.instantiate(
                    {a:self.value, Q:equality.rhs, 
                     R:equality.lhs})
        else:
            raise TypeError("'condition_equivalence_or_equality' must "
                            "represent a logical equivalence (Iff) or "
                            "equality (equals), got %s."
                             %condition_equivalence_or_equality)
        raise ValueError("%s expected to have %s on one of its sides"
                         %(condition_equivalence_or_equality,
                           self.condition))

    @equality_prover('sub_expr_substituted', 'sub_expr_substitute')
    def sub_expr_substitution(self, new_sub_exprs, **defaults_config):
        '''
        Given new sub-expressions to replace existing sub-expressions,
        return the equality between this Expression and the new
        one with the new sub-expressions.
        '''
        from proveit.logic import Equals
        from proveit.relation import TransRelUpdater
        assert len(new_sub_exprs)==2, (
                "Expecting 2 sub-expressions: value and condition")
        eq = TransRelUpdater(self)
        expr = self
        if new_sub_exprs[0] != self.sub_expr(0):
            expr = eq.update(expr.value_substitution(
                    Equals(self.sub_expr(0), new_sub_exprs[0])))
        if new_sub_exprs[1] != self.sub_expr(1):
            expr = eq.update(expr.conditional_substitution(
                    Equals(self.sub_expr(1), new_sub_exprs[1])))
        return eq.relation
    
    def readily_equal(self, rhs):
        '''
        We can readily equate conditionals with the same condition and
        readily equal values.
        '''
        from proveit.logic import Equals
        if not isinstance(rhs, Conditional):
            return False
        if not self.condition == rhs.condition:
            # conditions must match
            return False
        return Equals(self.value, rhs.value).readily_provable()
    
    @equality_prover('equated', 'equate')
    def deduce_equal(self, rhs, **defaults_config):
        '''
        We can equate conditionals with the same condition and provably
        equal values.
        '''
        from proveit.logic import Equals
        lhs = self
        if (isinstance(rhs, Conditional) and 
                lhs.condition==rhs.condition):
            value_eq = Equals(lhs.value, rhs.value)
            value_eq.prove(assumptions=defaults.assumptions+(self.condition,))
            return lhs.value_substitution(value_eq)
        raise NotImplementedError("Conditional.deduce_equal only implemented "
                                  "for equating Conditionals with the same "
                                  "condition.")
