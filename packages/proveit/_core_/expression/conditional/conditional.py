from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.composite import compositeExpression
from proveit._core_.defaults import USE_DEFAULTS

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
        self.values = compositeExpression(value_or_values)
        if len(self.values) == 1:
            # has a single value
            self.value = self.values[0]
            self.value_or_values = self.value
        else:
            self.value_or_values = self.values
        self.conditions = compositeExpression(value_or_values)
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
        inner_str = '; '.join(value.string() + ' | ' + condition.string() \
                              for value, condition in zip(self.values, 
                                                          self.conditions))
        return '{' + inner_str +'}'
    
    def latex(self, **kwargs):
        inner_str = r' \\ '.join(value.latex() + ' & | &  ' + condition.latex() \
                                  for value, condition in zip(self.values, 
                                                              self.conditions))
        inner_str = r'\begin{array}{ccc}' + inner_str + r'\end{array}'
        inner_str = r'\left\{' + inner_str + r'\right.'
        if kwargs.get('fence', False):
            return r'\left[' + inner_str + r'\right] '
        return inner_str
    
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        from proveit.logic import EvaluationError, TRUE
        for condition in self.conditions:
            if condition == TRUE:
                return value # ACTUALLY, THIS MUST BE PROVED
        raise EvaluationError(self, assumptions)
    
    def substituted(self, exprMap, relabelMap=None, reservedVars=None,
                    assumptions=USE_DEFAULTS):
        '''
        Return this expression with its variables substituted 
        according to exprMap and/or relabeled according to relabelMap.
        If one of the conditions is known to be true, simply return
        the value corresonding to that condition.  Otherwise,
        return the Conditional with substituted values and conditions.
        '''
        
        # Do the substitution for the conditions and see if any are Known to be
        # true.  If it is return the corresponding value.
        subbed_conditions = []
        for value, condition in zip(self.values, self.conditions):
            subbed_cond =condition.substituted(exprMap, relabelMap, reservedVars, 
                                               assumptions)
            if subbed_cond.proven(assumptions):
                return value.substituted(exprMap, relabelMap, reservedVars,
                                         assumptions)
            subbed_conditions.append(subbed_cond)
            
        subbed_values = []
        for value, subbed_con in zip(self.values, subbed_conditions):
            subbed_val = value.substituted(exprMap, relabelMap, reservedVars,
                                           assumptions+[subbed_cond])
            subbed_values.append(subbed_val)
        return Conditional(subbed_values, subbed_conditions)
