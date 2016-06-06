from label import Label
from proveit._core_.expression.expr import MakeNotImplemented, ScopingViolation, ImproperRelabeling

class Variable(Label):
    """
    A Variable is an interchangeable label.  They may be relabeled Variable to Variable.
    Through specialization of a Forall statement over one or more Variables, those Variables
    may each be substituted with a general Expression.
    """    
    def __init__(self, stringFormat, latexFormat=None):
        '''
        Create a Variable.  If latexFormat is not supplied, the stringFormat is used for both.
        '''
        Label.__init__(self, stringFormat, latexFormat, 'Variable')

    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != Variable: 
            raise MakeNotImplemented(subClass)
        return Label._make(subClass, coreInfo, subExpressions)
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        '''
        Returns this expression with the variables substituted 
        according to subMap and/or relabeled according to relabelMap.
        '''
        from proveit._core_.expression.expr import Expression
        if (exprMap is not None) and (self in exprMap):
            subbed = exprMap[self]
            if not isinstance(subbed, Expression):
                raise TypeError('Must substitute a Variable with an Expression')
            return subbed._restrictionChecked(reservedVars)
        elif relabelMap is not None:
            subbed = relabelMap.get(self, self)
            if not isinstance(subbed, Variable):
                raise ImproperRelabeling('May only relabel Variable to Variable')
            if reservedVars is not None and subbed in reservedVars.keys():
                if self != reservedVars[subbed]:
                    raise ScopingViolation("Relabeling in violation of Variable scoping restrictions.")
            return subbed
        return self
        
    def usedVars(self):
        return {self}
        
    def freeVars(self):
        return {self}

    def freeMultiVars(self):
        return set() # overridden in MultiVariable

class DummyVariable(Variable):
    def __init__(self, n):
        Variable.__init__(self, '_' + str(n) + '_', latex = r'\_' + str(n) + r'\_')

def safeDummyVar(*expressions):
    usedVs = frozenset().union(*[expr.usedVars() for expr in expressions])
    i = 0
    while DummyVariable(i) in usedVs:
        i += 1
    return DummyVariable(i)
