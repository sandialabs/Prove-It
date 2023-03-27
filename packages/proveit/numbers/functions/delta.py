from proveit import Operation, Literal

class KroneckerDelta(Operation):
    '''
    The Kronecker delta function of i and j is equal to 1 if
    i=j or equals 0 otherwise.
    '''

    _operator_ = Literal(string_format='Kdelta', theory=__file__)

    def __init__(self, i, j, *, styles=None):
        '''
        Kronecker delta of i and j.
        '''
        Operation.__init__(self, KroneckerDelta._operator_, (i, j),
                           styles=styles)

    def string(self, **kwargs):
        return ('delta_{' + self.operands[0].string(fence=True) + ', '
                         + self.operands[1].string(fence=True) + '}')

    def latex(self, **kwargs):
        return (r'\delta_{' + self.operands[0].string(fence=True) + ', '
                         + self.operands[1].string(fence=True)) + '}'
