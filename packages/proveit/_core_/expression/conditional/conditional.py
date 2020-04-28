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
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        from proveit.logic import EvaluationError, TRUE
        for condition in self.conditions:
            if condition == TRUE:
                return value # ACTUALLY, THIS MUST BE PROVED
        raise EvaluationError(self, assumptions)
    '''
    
    def substituted(self, repl_map, assumptions=USE_DEFAULTS, 
                    requirements=None):
        '''
        Returns this expression with sub-expressions substituted 
        according to the replacement map (repl_map) dictionary.
        
        'assumptions' and 'requirements' are used when an operator is
        substituted by a Lambda map that has iterated parameters such that 
        the length of the parameters and operands must be proven to be equal.
        For more details, see Operation.substituted, Lambda.apply, and
        Iter.substituted (which is the sequence of calls involved).
        
        For a Conditional, the 'condition' is added to the assumptions 
        when 'substituted' is called on the 'value'.
        '''
        from proveit import ExprRange
        from proveit._common_ import a, b
        from proveit.logic import And, TRUE
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]
        
        if requirements is None: requirements = []
        
        value = self.value
        condition = self.condition        
        
        # First perform substitution on the conditions:
        subbed_cond = condition.substituted(repl_map, 
                                            assumptions, requirements)

        # Next perform substitution on the value, adding the condition
        # as an assumption.            
        assumptions = defaults.checkedAssumptions(assumptions)
        subbed_val = value.substituted(repl_map, assumptions+(subbed_cond,),
                                       requirements)

        substituted = Conditional(subbed_val, subbed_cond)

        reduction = None

        if defaults.reduce_conditionals_with_no_conditions and \
                isinstance(subbed_cond, And) and len(subbed_cond.operands)==0:
            # Automatically reduce a conditional with no conditions
            # (just an empty conjunction which evaluates to True)
            # to just the substituted value.
            from proveit.core_expr_types.conditionals._theorems_ import \
                no_condition_reduction
            try:
                defaults.reduce_conditionals_with_no_conditions = False
                reduction = no_condition_reduction.instantiate({a:subbed_val})
            finally:
                defaults.reduce_conditionals_with_no_conditions = True
        elif defaults.reduce_conditionals_with_true_condition and \
                subbed_cond == TRUE:
            # Automatically reduce a conditional with a TRUE
            # condition to just the substituted value.
            from proveit.core_expr_types.conditionals._axioms_ import \
                true_condition_reduction
            try:
                defaults.reduce_conditionals_with_true_condition = False
                reduction = true_condition_reduction.instantiate({a:subbed_val})
            finally:
                defaults.reduce_conditionals_with_true_condition = True
        elif defaults.reduce_conditionals_with_singular_conditions and \
                isinstance(subbed_cond, And) and len(subbed_cond.operands)==1 \
                and not isinstance(subbed_cond.operands[0], ExprRange):
            from proveit.core_expr_types.conditionals._theorems_ import \
                single_condition_reduction
            try:     
                defaults.reduce_conditionals_with_singular_conditions = False
                reduction = single_condition_reduction.instantiate(
                        {a:subbed_val, b:subbed_cond.operands[0]})
            finally:
                defaults.reduce_conditionals_with_singular_conditions = True


        if reduction is not None:
            from proveit import KnownTruth
            from proveit.logic import Equals
            assert(isinstance(reduction, KnownTruth))
            assert(isinstance(reduction.expr, Equals))
            assert(reduction.expr.lhs == substituted)
            requirements.append(reduction)
            return reduction.expr.rhs
        
        return substituted        

