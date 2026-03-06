from proveit import Function, Literal

class Identity(Function):
    '''
    Represents the n x n identity matrix associated with the identity
    map of a vector space. The identity map is a linear map that maps
    any any element of a vector space to itself.
    '''

    _operator_ = Literal(string_format='1',
            latex_format=r'\mathbbm{1}', theory=__file__)

    def _config_latex_tool(self, lt):
        if 'bbm' not in lt.packages:
           lt.packages.append('bbm')

    def __init__(self, size, *, styles=None):
        '''
        Initialize a representation of a (size x size) identity matrix
        associated with the identity map on a vector space.
        For example, the 3 x 3 identity matrix on R^3 could be
        intialized with Identity(num(3)).

        '''
        Function.__init__(self, Identity._operator_, size,
                          styles=styles)

    def string(self, **kwargs):
        return self.operator.string() + '_' + (
                self.operand.string(fence=True))

    def latex(self, **kwargs):
        return self.operator.latex() + '_{' + (
                self.operand.latex(fence=True) + '}')
