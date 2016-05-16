from label import Label
from proveit.core.expression.expr import MakeNotImplemented, ScopingViolation, ImproperRelabeling

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
        May expand to an expr_list.
        '''
        from proveit.core.expression.bundle.bundle import isBundledVar
        from proveit.core.expression.composite.expr_list import ExpressionList
        if (exprMap is not None) and (self in exprMap):
            return exprMap[self]._restrictionChecked(reservedVars)
        elif relabelMap != None:
            subbed = relabelMap.get(self, self)
            for subVar in (subbed if isinstance(subbed, ExpressionList) else [subbed]):
                if not isinstance(subVar, Variable) and not isBundledVar(subVar):
                    raise ImproperRelabeling('May only relabel a Variable with Variable(s) and/or Bundled Variable(s)')
                if reservedVars != None and subVar in reservedVars.keys():
                    if self != reservedVars[subVar]:
                        raise ScopingViolation("Relabeling in violation of Variable scoping restrictions.")
            return subbed
        else:
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
