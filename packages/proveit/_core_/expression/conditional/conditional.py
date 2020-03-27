from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.defaults import defaults, USE_DEFAULTS

class Conditional(Expression):
    '''
    A Conditional expression is one that has values corresponding with
    conditions.  The Conditional evaluates to any of the values whose
    corresponding condition is TRUE.  If more than one condition is TRUE,
    all corresponding values are presumed to be equal to each other.
    If none of the conditions are TRUE, the Conditional cannot be simplified
    to any of the values.
    '''
    
    def __init__(self, value_or_values, condition_or_conditions):    
        from proveit._core_.expression.composite.composite import compositeExpression

        self.values = compositeExpression(value_or_values)
        if len(self.values) == 1:
            # has a single value
            self.value = self.values[0]
            self.value_or_values = self.value
        else:
            self.value_or_values = self.values
        self.conditions = compositeExpression(condition_or_conditions)
        if len(self.conditions) == 1:
            # has a single value
            self.condition = self.conditions[0]
            self.condition_or_conditions = self.condition
        else:
            self.condition_or_conditions = self.conditions
        if len(self.values) != len(self.conditions):
            raise ValueError("The number of values must match the number of "
                             "conditions in a Conditional.")
        Expression.__init__(self, ['Conditional'], (self.value_or_values, 
                                                    self.condition_or_conditions))
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if len(coreInfo) != 1 or coreInfo[0] != 'Conditional':
            raise ValueError("Expecting Conditional coreInfo to contain exactly "
                             ":one item: 'Conditional'")
        if subClass != Conditional: 
            raise MakeNotImplemented(subClass)
        if len(subExpressions) != 2:
            raise ValueError("Expecting Conditional to have two sub-expressions.")
        value_or_values, condition_or_conditions = subExpressions
        return Conditional(value_or_values, condition_or_conditions) \
                .withStyles(**styles)
    
    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Indexed.
        '''
        yield self.value_or_values
        yield self.condition_or_conditions
    
    def string(self, **kwargs):
        inner_str = '; '.join(value.string() + ' if ' + condition.string() \
                              for value, condition in zip(self.values, 
                                                          self.conditions))
        return '{' + inner_str +'}'
    
    def latex(self, **kwargs):
        inner_str = r' \\ '.join(value.latex() + r' & \textrm{if} &  ' + condition.latex() \
                                  for value, condition in zip(self.values, 
                                                              self.conditions))
        inner_str = r'\begin{array}{ccc}' + inner_str + r'\end{array}'
        inner_str = r'\left\{' + inner_str + r'\right.'
        if kwargs.get('fence', False):
            return r'\left[' + inner_str + r'\right] '
        return inner_str
    
    '''
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        from proveit.logic import EvaluationError, TRUE
        for condition in self.conditions:
            if condition == TRUE:
                return value # ACTUALLY, THIS MUST BE PROVED
        raise EvaluationError(self, assumptions)
    '''
    
    def substituted(self, repl_map, reserved_vars=None,
                    assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with sub-expressions substituted 
        according to the replacement map (repl_map) dictionary.
        
        reserved_vars is used internally to protect the "scope" of a
        Lambda map.  For more details, see the Lambda.substitution
        documentation.

        'assumptions' and 'requirements' are used when an operator is
        substituted by a Lambda map that has iterated parameters such that 
        the length of the parameters and operands must be proven to be equal.
        For more details, see Operation.substituted, Lambda.apply, and
        Iter.substituted (which is the sequence of calls involved).
        
        For a Conditional, a condition is added to the assumptions when 
        'substituted' is called on the value corresponding to that condition.
        '''
            
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]._restrictionChecked(reserved_vars)
        
        subbed_values = []
        subbed_conditions = []
        if requirements is None: requirements = []
        for value, condition in zip(self.values, self.conditions):
            # First perform substitution on the conditions:
            subbed_cond = condition.substituted(repl_map, reserved_vars, 
                                                assumptions, requirements)
            subbed_conditions.append(subbed_cond)
            # Next perform substitution on the value, adding the condition
            # as an assumption.            
            assumptions = defaults.checkedAssumptions(assumptions)
            subbed_val = value.substituted(repl_map, reserved_vars,
                                           assumptions+(subbed_cond,),
                                           requirements)
            subbed_values.append(subbed_val)
        return Conditional(subbed_values, subbed_conditions)
    
        