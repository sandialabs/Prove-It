from proveit import Literal, Operation, maybe_fenced_string

class MatrixExp(Operation):
    '''
    Matrix dot product of any number of operands.
    '''

    _operator_ = Literal(string_format='ExpM', theory=__file__)

    def __init__(self, base, exponent, *, styles=None):
        r'''
        Raise matrix 'base' to exponent power.
        '''
        self.base = base
        self.exponent = exponent
        Operation.__init__(self, MatrixExp._operator_, (base, exponent),
                           styles=styles)

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, **kwargs):
        # begin building the inner_str
        inner_str = self.base.formatted(
            format_type, fence=True, force_fence=True)
        inner_str = (
            inner_str
            + r'^{' + self.exponent.formatted(format_type, fence=False)
            + '}')
        # only fence if force_fence=True (nested exponents is an
        # example of when fencing must be forced)
        kwargs['fence'] = (
            kwargs['force_fence'] if 'force_fence' in kwargs else False)
        return maybe_fenced_string(inner_str, **kwargs)
