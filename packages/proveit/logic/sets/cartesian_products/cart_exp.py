from proveit import (Operation, Literal, relation_prover,
                     prover, maybe_fenced_string)
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

    def membership_object(self, element):
        from .cart_exp_membership import CartExpMembership
        return CartExpMembership(element, self)

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

    @relation_prover
    def deduce_as_vec_space(self, **defaults_config):
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
    
    def containing_vec_space(self, field, **defaults_config):
        '''
        Return a vector space over the given field which contains
        this Cartesian exponentiation.  Specifically.
            C^n contains R^n and Q^n as well as C^n
            R^n contains Q^n as well as R^n
            Q^n only contains Q^n
        '''
        from proveit.numbers import Rational, Real, Complex
        if field is None or field==self.base:
            vec_space = self
        elif ((field == Complex and self.base in (Rational, Real))
              or (field == Real and self.base == Rational)):
            vec_space = CartExp(field, self.exponent)
        else:
            raise NotImplementedError("'containing_vec_space' is not implemented "
                                      "to handle %s over field %s"
                                      %(self, field))
        vec_space.deduce_as_vec_space()
        return vec_space
        
