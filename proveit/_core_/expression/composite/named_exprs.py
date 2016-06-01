from composite import Composite
from proveit._core_.expression.expr import Expression, MakeNotImplemented
import re

class NamedExpressions(Composite, Expression, dict):
    """
    An NamedExpressions is a composite expr that maps strings to Expressions.
    """
    def __init__(self, expr_dict):
        from proveit._core_.expression.bundle.etcetera import Etcetera
        dict.__init__(self, expr_dict)
        for key, val in expr_dict.iteritems():
            if not isinstance(key, str): 
                raise TypeError("Keywords of an expression dictionary may only be strings")
            if not re.match('[A-Za-z0-9_]+', key):
                raise ValueError('A NamedExpression key may only include alphanumeric or underscore chararcters.')
            if not isinstance(val, Expression): 
                raise TypeError("Values of an expression dictionary must be Expressions")
            if isinstance(val, Etcetera):
                raise TypeError('An Etcetera may be contained in an ExpressionList but not in a NamedExpressions')
        Expression.__init__(self, ['NamedExpressions', ','.join(sorted(self.keys()))], [self[key] for key in sorted(self.keys())])

    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != NamedExpressions: 
            MakeNotImplemented(subClass) 
        if len(coreInfo) != 2:
            raise ValueError("Expecting NamedExpressions coreInfo to contain excactly 2 items: 'NamedExpressions' and the keys")
        if coreInfo[0] != 'NamedExpressions':
            raise ValueError("Expecting NamedExpressions coreInfo[0] to be 'NamedExpressions'")
        keys = coreInfo[1].split(',')
        if len(subExpressions) != len(keys):
            raise ValueError("The number of sub-expressions, " + str(len(subExpressions)), ", expected to match the number of the NamedExpressions' keys, ", str(len(keys)))
        return NamedExpressions({key:subExpression for key, subExpression in zip(keys, subExpressions)})        
        
    def string(self):
        return '{' + ', '.join(key + ':' + self[key].string(fence=True) for key in sorted(self.keys())) + '}'

    def latex(self):
        outStr = r'\left\{ \begin{array}{l}' + '\n'
        for key in sorted(self.keys()):
            outStr += r'{\rm ' + key.replace('_', r'\_') + r'}: ' + self[key].latex(fence=True) + r'\\' + '\n'
        outStr += r'\end{array} \right\}' + '\n'
        return outStr            
    
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the substitutions made 
        according to exprMap and/or relabeled according to relabelMap.
        '''
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        else:
            return NamedExpressions({key:expr.substituted(exprMap, relabelMap, reservedVars) for key, expr in self.iteritems()})

    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self.values()])
        
    def freeVars(self):
        '''
        Returns the union of the free Variables of the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self.values()])

    def freeMultiVars(self):
        """
        Returns the union of the free MultiVariables of the sub-Expressions.
        """
        return set().union(*[expr.freeMultiVars() for expr in self.values()])
