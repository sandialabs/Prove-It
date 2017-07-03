from composite import Composite
from proveit._core_.expression.expr import Expression, MakeNotImplemented
import re

class NamedExpressions(Composite, Expression):
    """
    An NamedExpressions is a composite expr that maps strings to Expressions.
    """
    def __init__(self, items):
        '''
        Create a NamedExpressions Expression object from a list (iterable) of
        (keyword, Expression) pairs, where each keyword is a string.
        '''
        from proveit._core_.expression.bundle.etcetera import Etcetera
        from proveit._core_ import KnownTruth
        keywords = []
        elems = dict()
        for key, val in items:
            keywords.append(key)
            elems[key] = val
            if not isinstance(key, str): 
                raise TypeError("Keywords of an expression dictionary may only be strings")
            if not re.match('[A-Za-z0-9_]+', key):
                raise ValueError('A NamedExpression key may only include alphanumeric or underscore chararcters.')
            if isinstance(val, KnownTruth):
                val = val.expr # extract the Expression from the KnownTruth
            if not isinstance(val, Expression): 
                raise TypeError("Values of an expression dictionary must be Expressions")
            if isinstance(val, Etcetera):
                raise TypeError('An Etcetera may be contained in an ExpressionList but not in a NamedExpressions')
        self.keywords, self.elems = keywords, elems
        Expression.__init__(self, ['NamedExpressions'] + self.keys(), [self[key] for key in self.keys()])

    def __getitem__(self, key):
        return self.elems[key]

    def __contains__(self, key):
        return key in self.elems
                        
    def __len__(self):
        return len(self.elems)
        
    def __iter__(self):
        return iter(self.elems)
        
    def iteritems(self):
        return self.elems.iteritems()

    def itervalues(self):
        return self.elems.itervalues()
    
    def keys(self):
        return self.keywords

    def values(self):
        return [self.elems[key] for key in self.keywords]

    def buildArguments(self):
        '''
        Yield the argument (name, value) pairs that could be used to 
        recreate the NamedExpressions.  Wrap the names in quotation marks
        '''
        for name, expr in self.iteritems():
            yield ('"' + str(name) + '"', expr)
            
    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != NamedExpressions: 
            MakeNotImplemented(subClass) 
        if coreInfo[0] != 'NamedExpressions':
            raise ValueError("Expecting NamedExpressions coreInfo[0] to be 'NamedExpressions'")
        keys = coreInfo[1:]
        if len(subExpressions) != len(keys):
            raise ValueError("The number of sub-expressions, " + str(len(subExpressions)), ", expected to match the number of the NamedExpressions' keys, ", str(len(keys)))
        return NamedExpressions([(key,subExpression) for key, subExpression in zip(keys, subExpressions)])        
        
    def string(self, **kwargs):
        return '{' + ', '.join(key + ':' + self[key].string(fence=True) for key in self.keys()) + '}'

    def latex(self, **kwargs):
        outStr = r'\left\{ \begin{array}{l}' + '\n'
        for key in self.keys():
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
            return NamedExpressions([(key,expr.substituted(exprMap, relabelMap, reservedVars)) for key, expr in self.iteritems()])

    def usedVars(self):
        '''
        Returns the union of the used Variables of the sub-Expressions.
        '''
        return set().union(*[expr.usedVars() for expr in self.elems.values()])
        
    def freeVars(self):
        '''
        Returns the union of the free Variables of the sub-Expressions.
        '''
        return set().union(*[expr.freeVars() for expr in self.elems.values()])

    def freeMultiVars(self):
        """
        Returns the union of the free MultiVariables of the sub-Expressions.
        """
        return set().union(*[expr.freeMultiVars() for expr in self.elems.values()])
