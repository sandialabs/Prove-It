from .expr_array import ExprArray

class VertExprArray(ExprArray):
    '''
    An ExprArray represented in column-major order.
    '''
    
    def __init__(self, *expressions, styles=None):
        '''
        Initialize an ExprArray from an iterable over ExprTuple
        objects or Expressions that represent ExprTuples.
        '''
        ExprArray.__init__(self, *expressions, styles=styles)
    
    def latex(self, fence=False, **kwargs):
        return ExprArray.latex(self, orientation='vertical', fence=fence,
                               **kwargs)

    def _config_latex_tool(self, lt):
        ExprArray._config_latex_tool(self, lt)
        if 'multirow' not in lt.packages:
            lt.packages.append('multirow')
