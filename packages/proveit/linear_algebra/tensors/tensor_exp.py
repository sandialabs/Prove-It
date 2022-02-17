from proveit import Literal, Operation, prover, equality_prover
from proveit import m, n, K, V
from proveit.logic import SetMembership, CartExp
from proveit.linear_algebra import VecSpaces
                                    
class TensorExp(Operation):
    '''
    A Tensor exponentation represents a tensor product repeated a
    whole number of times.
    '''

    # the literal operator of the TensorExp operation
    _operator_ = Literal(string_format=r'TensorExp', theory=__file__)

    def __init__(self, base, exponent, *, styles=None):
        r'''
        Tensor exponentiation to any natural number exponent.
        '''
        Operation.__init__(self, TensorExp._operator_, (base, exponent),
                           styles=styles)
        self.base = self.operands[0]
        self.exponent = self.operands[1]
    
    def membership_object(self, element):
        return TesorExpMembership(element, self)

    def _formatted(self, format_type, fence=True):
        # changed from formatted to _formatted 2/14/2020 (wdc)
        formatted_base = self.base.formatted(format_type, 
                                             fence=True, force_fence=True)
        formatted_exp = self.exponent.formatted(format_type, fence=True,
                                                force_fence=True)
        if format_type == 'latex':
            return formatted_base + r'^{\otimes ' + formatted_exp + '}'
        elif format_type == 'string':
            return formatted_base + '^{otimes ' + formatted_exp + '}'

    @equality_prover('do_reduced_simplified', 'do_reduced_simplify')
    def do_reduced_simplification(self, **defaults_config):
        '''
        For the trivial cases of a one exponent, derive and return
        this tensor-exponentiated expression equated with a simplified
        form. Assumptions may be necessary to deduce necessary
        conditions for the simplification. For example,
        TensorExp(x, one).do_reduced_simplification()
        '''
        from proveit.numbers import zero, one
        from . import tensor_exp_one
        if self.exponent == one:
            return tensor_exp_one.instantiate({x: self.base})
        raise ValueError('Only trivial simplification is implemented '
                         '(tensor exponent of one). Submitted tensor '
                         'exponent was {}.'.format(self.exponent))

class TesorExpMembership(SetMembership):
    '''
    Defines methods that apply to membership in a TensorProd
    (i.e. membership in a tensor product).
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Derive the broader membership as a CartExp as a side-effect.
        '''
        yield self.derive_cartexp_membership
    
    @prover
    def derive_cartexp_membership(self, **defaults_config):
        '''
        Derive membership in the CartExp which is a superset of the
        TensorExp.
        '''
        from . import tensor_exp_inclusion, tensor_exp_of_cart_exp_inclusion
        if isinstance(self.domain.base, CartExp):
            _V = self.domain.base
            _K = VecSpaces.known_field(_V)
            _m = self.domain.base.exponent
            _n = self.domain.exponent
            inclusion = tensor_exp_of_cart_exp_inclusion.instantiate(
                    {V:_V, K:_K, m:_m, n:_n})
        else:
            _V = self.domain.base
            _K = VecSpaces.known_field(_V)
            _n = self.domain.exponent
            inclusion = tensor_exp_inclusion.instantiate(
                    {V:_V, K:_K, n:_n})
        return inclusion.derive_superset_membership(self.element)
