from bundle import Bundle
from proveit._core_.expression.expr import MakeNotImplemented
from proveit._core_.expression.composite.expr_list import ExpressionList

class Etcetera(Bundle):
    def __init__(self, expr):
        Bundle.__init__(self, ExpressionList, expr, lambda expr : Etcetera(expr))

    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != Etcetera: 
            MakeNotImplemented(subClass) 
        if len(coreInfo) != 1 or coreInfo[0] != 'Etcetera':
            raise ValueError("Expecting Etcetera coreInfo to contain exactly one item: 'Etcetera'")
        if len(subExpressions) != 1:
            raise ValueError("Expecting exactly one sub-expression to make an Etcetera")
        return Etcetera(subExpressions[0])  

    def buildArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Etcetera expression.
        '''
        yield self.subExpr(0)

    def string(self, **kwargs):
        return '..' + self.bundledExpr.string(fence=True) + '..'
    
    def latex(self, **kwargs):
        return '..' + self.bundledExpr.latex(fence=True) + '..'
