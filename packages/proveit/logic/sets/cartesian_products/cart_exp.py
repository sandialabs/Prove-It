from proveit import (Operation, Literal, relation_prover,
                     prover, maybe_fenced_string)
from proveit import m, n, A, B

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

    @prover
    def deduce_subset_eq_relation(self, subset, **defaults_config):
        '''
        Prove that this CartExp is a SubsetEq of 'subset' if
        the 'subset' is also a CartExp with the same exponent,
        and the base of self is a SubsetEq of the base of 'subset'.
        '''
        from . import cart_exp_subset_eq
        if not isinstance(subset, CartExp) or subset.exponent != self.exponent:
            raise NotImplementedError(
                    "CartExp.deduce_subset_eq_relation only implemented "
                    "to derive a subset relation between CartExp "
                    "expressions with the same exponent")
        return cart_exp_subset_eq.instantiate(
                {m:self.exponent, A:subset.base, B:self.base})

    @prover
    def deduce_as_vec_space(self, field=None, **defaults_config):
        '''
        Prove that this CartExp expression is contained in the class
        of vector spaces over some field.
        '''
        from proveit.linear_algebra import deduce_as_vec_space
        # return deduce_as_vec_space(self) # <- produces inf loop
        '''
        For the Cartesian exponentiation of rational, real, or
        complex numbers, we can deduce that it is a member of
        the class of vector spaces over the corresponding field.
        '''
        from proveit.numbers import Rational, Real, Complex
        from proveit.linear_algebra import (
                rational_vec_set_is_vec_space, real_vec_set_is_vec_space, 
                complex_vec_set_is_vec_space)
        if self.base == Rational:
            membership = rational_vec_set_is_vec_space.instantiate(
                    {n:self.exponent})
        elif self.base == Real:
            membership = real_vec_set_is_vec_space.instantiate({n:self.exponent})
        elif self.base == Complex:
            membership = complex_vec_set_is_vec_space.instantiate({
                    n:self.exponent})
        else:
            raise NotImplementedError(
                    "'deduce_as_vec_space' is not implemented "
                    "to handle %s"%expr)

        return membership
