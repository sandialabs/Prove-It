from proveit import Operation, Literal
from proveit import maybe_fenced_string, maybe_fenced_latex

class Conjugate(Operation):
    '''
    The complex conjugate of a + i b for real numbers a and b is
    equal to a - i b.
    '''

    _operator_ = Literal(string_format='conj', theory=__file__)

    def __init__(self, num, *, styles=None):
        '''
        Create an expression for the complex conjugate of the given
        number.
        '''
        Operation.__init__(self, Conjugate._operator_, num,
                           styles=styles)

    def string(self, **kwargs):
        return maybe_fenced_string(
            self.operand.string(
                fence=True) + '*',
            **kwargs)

    def latex(self, **kwargs):
        return maybe_fenced_latex(
            self.operand.latex(
                fence=True) + "^*",
            **kwargs)