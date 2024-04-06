from proveit import Function, Literal

class Inverse(Function):
    '''
    Represents the inverse of a function.
    '''

    # operator of the Add operation FOR NATURAL NUMBERS ONLY
    _operator_ = Literal('Inv', theory=__file__)
    
    def __init__(self, function, *, styles=None):
        r'''
        Inverse of 'function'.
        '''
        Function.__init__(self, Inverse._operator_, function, 
                           styles=styles)
        self.function = function

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, **kwargs):
        # begin building the inner_str
        func_str = self.function.formatted(
            format_type, fence=True, force_fence=True)
        return (func_str + r'^{\leftarrow}')
