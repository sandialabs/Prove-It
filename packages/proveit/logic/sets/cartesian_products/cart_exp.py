from proveit import (Operation, Literal, relation_prover,
                     maybe_fenced_string)
from proveit import n

class CartExp(Operation):
    '''
    CartExp represents an exponentiation of a set by a positive, natural
    number to denote repeated Cartesion products.
    '''
    
    _operator_ = Literal(string_format='Exp', theory=__file__)
    
    def __init__(self, base, exponent, *, styles=None):
        Operation.__init__(self, CartExp._operator_, (base, exponent), 
                           styles=styles)
        self.base = base
        self.exponent = exponent

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

    @relation_prover
    def deduce_as_vec_space(self, *, field, **defaults_config):
        '''
        For the Cartesian exponentiation of rational, real, or
        complex numbers, we can deduce that it is a member of
        the class of vector spaces over the corresponding field.
        '''
        from proveit.numbers import Rational, Real, Complex
        from proveit.linear_algebra import (
                rational_vec_space, real_vec_space, complex_vec_space)
        if self.base == Rational:
            return rational_vec_space.instantiate({n:self.exponent})
        elif self.base == Real:
            return real_vec_space.instantiate({n:self.exponent})
        elif self.base == Complex:
            return complex_vec_space.instantiate({n:self.exponent})
        raise NotImplementedError("'deduce_as_vec_space' is not implemented "
                                  "to handle %s"%self)
