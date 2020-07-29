from proveit._core_.expression.expr import Expression, MakeNotImplemented
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
    
    def __init__(self, value, condition_or_conditions,
                 comma_delimited_conditions=True):  
        '''
        Create a Conditional with the given particular value
        and the given condition.  If multiple conditions are
        provided, these will be wrapped in a conjunction internally.
        However, if the 'condition_delimiter' style is set to ','
        (initially set according the the comma_delimited_conditions
        flag), the conditions will be displayed in a comma
        delimited fashion if it is within a conjunction.
        '''
        from proveit._core_.expression.composite import \
            singleOrCompositeExpression, Composite, ExprTuple, ExprRange
        styles = {'condition_delimiter' : 
                  'comma' if comma_delimited_conditions else 'and'}
        
        value = singleOrCompositeExpression(value)
        assert (isinstance(value, Expression) 
                and not isinstance(value, ExprRange))
            
        condition_or_conditions = \
            singleOrCompositeExpression(condition_or_conditions)
        
        if isinstance(condition_or_conditions, ExprTuple):
            if (len(condition_or_conditions) == 1 and
                    not isinstance(condition_or_conditions[0], ExprRange)):
                condition = condition_or_conditions[0]
            else:
                # Must wrap a tuple of conditions in a conjunction.
                from proveit.logic import And
                condition = And(*condition_or_conditions)
        else:
            condition = condition_or_conditions
        assert (isinstance(condition, Expression) and 
                not isinstance(condition, Composite))
        
        Expression.__init__(self, ['Conditional'], 
                            (value, condition), styles=styles)
        
        self.value = value
        self.condition = condition
    
    def styleOptions(self):
        from proveit import StyleOptions
        options = StyleOptions(self)
        options.addOption('condition_delimiter', ("'comma' or 'and'"))
        return options
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if len(coreInfo) != 1 or coreInfo[0] != 'Conditional':
            raise ValueError("Expecting Conditional coreInfo to contain exactly "
                             ":one item: 'Conditional'")
        if subClass != Conditional: 
            raise MakeNotImplemented(subClass)
        if len(subExpressions) != 2:
            raise ValueError("Expecting Conditional to have two sub-expressions.")
        value, condition = subExpressions
        return Conditional(value, condition) \
                .withStyles(**styles)
    
    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Indexed.
        '''
        yield self.value
        yield self.condition
    
    def _formatted_condition(self, formatType):
        from proveit.logic import And
        if self.getStyle('condition_delimiter') == 'comma':
            if (isinstance(self.condition, And) 
                    and len(self.condition.operands) > 1):
                return self.condition.operands.formatted(
                        formatType, fence=False, subFence=False, 
                        operatorOrOperators=', ')
        return self.condition.formatted(formatType)
    
    def string(self, **kwargs):
        formatted_condition = self._formatted_condition('string')
        inner_str = self.value.string() + ' if ' + formatted_condition
        if kwargs.get('fence', True) == True:
            return '{' + inner_str +'.'
        return inner_str
    
    def latex(self, **kwargs):
        formatted_condition = self._formatted_condition('latex')
        inner_str = (self.value.latex() + r' \textrm{ if } ' 
                     + formatted_condition)
        if kwargs.get('fence', True) == True:
            inner_str = r'\left\{' + inner_str + r'\right..'
        return inner_str
    
    '''
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS, **kwargs):
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
        from proveit import ExprRange
        from proveit._common_ import a, m, n, Q, R
        from proveit.logic import And, TRUE
        if self.condition == TRUE:
            from proveit.core_expr_types.conditionals._axioms_ import \
                true_condition_reduction
            return true_condition_reduction.instantiate({a:self.value})
        elif isinstance(self.condition, And):
            from proveit.core_expr_types.conditionals._theorems_ import \
                (singular_conjunction_condition_reduction,
                 condition_merger_reduction,
                 condition_append_reduction, condition_prepend_reduction,
                 condition_with_true_on_left_reduction,
                 condition_with_true_on_right_reduction)            
            conditions = self.condition.operands
            if len(conditions)==1 and not isinstance(conditions[0], ExprRange):
                with defaults.disabled_auto_reduction_types as disabled_types:
                    # Don't auto-reduce 'And' in this process
                    disabled_types.discard(And)
                    return singular_conjunction_condition_reduction \
                        .instantiate({a:self.value, Q:conditions[0]})
            elif (len(conditions)==2 and isinstance(conditions[0], And)):
                _Q = conditions[0].operands
                _m = _Q.length(assumptions)
                return condition_append_reduction.instantiate(
                        {a:self.value, m:_m, Q:_Q, R:conditions[1]},
                        assumptions=assumptions)
            elif (len(conditions)==2 and isinstance(conditions[1], And)):
                _R = conditions[1].operands
                _n = _R.length(assumptions)
                return condition_prepend_reduction.instantiate(
                        {a:self.value, n:_n, Q:conditions[0], R:_R},
                        assumptions=assumptions)                
            elif (len(conditions)==2 and
                    all(isinstance(cond, And) for cond in conditions)):
                _Q = conditions[0].operands
                _R = conditions[1].operands
                _m = _Q.length(assumptions)
                _n = _R.length(assumptions)
                _a = self.value
                return condition_merger_reduction.instantiate(
                        {m:_m, n:_n, a:_a, Q:_Q, R:_R},
                        assumptions=assumptions)
            elif (len(conditions)==2 and
                    any(isinstance(cond, And) for cond in conditions) and
                    any(cond==TRUE for cond in conditions)):
                if conditions[0]==TRUE:
                    thm = condition_with_true_on_left_reduction
                    _Q = conditions[1].operands
                else:
                    assert conditions[1]==TRUE
                    thm = condition_with_true_on_right_reduction  
                    _Q = conditions[0].operands
                _m = _Q.length(assumptions)
                _a = self.value
                return thm.instantiate({m:_m, a:_a, Q:_Q},
                                       assumptions=assumptions)
    
    def _replaced(self, repl_map, allow_relabeling,
                  assumptions, requirements, equality_repl_requirements):
        '''
        Returns this expression with sub-expressions replaced 
        according to the replacement map (repl_map) dictionary.
        
        'assumptions' and 'requirements' are used when an operator is
        replaced by a Lambda map that has iterated parameters such that 
        the length of the parameters and operands must be proven to be equal.
        For more details, see Operation.replaced, Lambda.apply, and
        Iter.replaced (which is the sequence of calls involved).
        
        For a Conditional, the 'condition' is added to the assumptions 
        when 'replaced' is called on the 'value'.
        '''
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be replaced.
            return repl_map[self]
        
        value = self.value
        condition = self.condition        
        
        # First perform substitution on the conditions:
        subbed_cond = condition.replaced(repl_map, allow_relabeling,
                                         assumptions, requirements,
                                         equality_repl_requirements)

        # Next perform substitution on the value, adding the condition
        # as an assumption.
        subbed_val = value.replaced(repl_map, allow_relabeling,
                                    assumptions+(subbed_cond,),
                                    requirements,
                                    equality_repl_requirements)

        return Conditional(subbed_val, subbed_cond)

