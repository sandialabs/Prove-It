from proveit import USE_DEFAULTS, equality_prover, prover
from proveit.linear_algebra import TensorProd
from proveit.logic import SetMembership, SetNonmembership
from proveit.numbers import num
from proveit import a, i, m, x, A, K, V


class TensorProdMembership(SetMembership):
    '''
    Defines methods that apply to membership in a TensorProd
    (i.e. membership in a tensor product).
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Unfold the enumerated set membership as a side-effect.
        '''
        # Actually just need an empty generator for now?
        yield from []
    #   yield self.unfold

    # @equality_prover('defined', 'define')
    # def definition(self, **defaults_config):
    #     '''
    #     Deduce and return 
    #         [element in (A union B ...)] = 
    #         [(element in A) or (element in B) ...]
    #     where self = (A union B ...).
    #     '''
    #     from . import union_def
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return union_def.instantiate(
    #             {m: _m, x: element, A: _A}, auto_simplify=False)

    # @prover
    # def unfold(self, **defaults_config):
    #     '''
    #     From [element in (A union B ...)], derive and return
    #     [(element in A) or (element in B) ...],
    #     where self represents [element in (A union B ...)].
    #     '''
    #     from . import membership_unfolding
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return membership_unfolding.instantiate(
    #         {m: _m, x: element, A: _A}, auto_simplify=False)

    # @prover
    # def conclude(self, **defaults_config):
    #     '''
    #     Called on self = [elem in (A U B U ...)], and knowing or
    #     assuming [[elem in A] OR [elem in B] OR ...], derive and
    #     return self.
    #     '''
    #     from . import membership_folding
    #     element = self.element
    #     operands = self.domain.operands
    #     _A = operands
    #     _m = _A.num_elements()
    #     return membership_folding.instantiate({m: _m, x: element, A: _A})


    @prover
    def conclude(self, **defaults_config):

        '''
        Called on self = [elem in (A x B x ...)] (where x denotes
        a tensor product and elem = a x b x ...) and knowing or
        assuming that (a in A) and (b in B) and ..., derive and
        return self.
        '''
        if isinstance(self.element, TensorProd):
            from . import tensor_prod_is_in_tensor_prod_space
            from proveit.linear_algebra import VecSpaces
            # we will need the domain acknowledged as a VecSpace
            # so we can later get its underlying field
            self.domain.deduce_as_vec_space()
            _a_sub = self.element.operands
            _i_sub = _a_sub.num_elements()
            _K_sub = VecSpaces.known_field(self.domain)
            vec_spaces = self.domain.operands

            return tensor_prod_is_in_tensor_prod_space.instantiate(
                    {a: _a_sub, i: _i_sub, K: _K_sub,  V: vec_spaces})

        raise ValueError("Element {0} is not a TensorProd.".
                         format(self.element))
