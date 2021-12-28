from proveit import USE_DEFAULTS, equality_prover, Lambda, prover
from proveit.linear_algebra import ScalarMult, TensorProd, VecSum
from proveit.logic import SetMembership, SetNonmembership
from proveit.numbers import num
from proveit import a, b, f, i, j, m, x, A, K, Q, V


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

        if isinstance(self.element, ScalarMult):
            from proveit.linear_algebra.scalar_multiplication import (
                    scalar_mult_closure)
            from proveit.linear_algebra import VecSpaces
            self.domain.deduce_as_vec_space()
            _V_sub = VecSpaces.known_vec_space(self.element.scaled, field=None)
            _K_sub = VecSpaces.known_field(_V_sub)
            _a_sub = self.element.scalar
            _x_sub = self.element.scaled
            return scalar_mult_closure.instantiate(
                    {V: _V_sub, K: _K_sub, a: _a_sub, x: _x_sub})

        if isinstance(self.element, VecSum):
            from proveit.linear_algebra.addition import summation_closure
            from proveit.linear_algebra import VecSpaces
            self.domain.deduce_as_vec_space()
            print("HERE!")
            _V_sub = VecSpaces.known_vec_space(self.element.summand)
            _K_sub = VecSpaces.known_field(_V_sub)
            _b_sub = self.element.indices
            _j_sub = _b_sub.num_elements()
            _f_sub = Lambda(self.element.indices, self.element.summand)
            _Q_sub = Lambda(self.element.indices, self.element.condition)
            imp = summation_closure.instantiate(
                        {V: _V_sub, K: _K_sub, b: _b_sub, j: _j_sub,
                         f: _f_sub, Q: _Q_sub})
            return imp.derive_consequent()

        raise ValueError("Element {0} is neither a TensorProd "
                         "nor a ScalarMult.".format(self.element))
