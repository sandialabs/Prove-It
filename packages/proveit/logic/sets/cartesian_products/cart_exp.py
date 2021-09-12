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


