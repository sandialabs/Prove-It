from proveit import Function, Literal

class Identity(Function):
    '''
    The identity map of a vector space is a linear map that maps
    any element to itself.
    '''

    _operator_ = Literal(string_format='1',latex_format=r'\mathbbm{1}', theory=__file__)

    def _config_latex_tool(self, lt):
        if 'bbm' not in lt.packages:
           lt.packages.append('bbm')

    def __init__(self,size, *, styles=None):
        '''
        Denote the set of linear maps that map from and to the given
        vectors spaces.
        '''
        Function.__init__(self, Identity._operator_, size,
                          styles=styles)

    def string(self, **kwargs):
        return self.operator.string() + '_' + (
                self.operand.string(fence=True))

    def latex(self, **kwargs):
        return self.operator.latex() + '_{' + (
                self.operand.latex(fence=True) + '}')
