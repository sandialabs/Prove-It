from proveit import (USE_DEFAULTS, equality_prover, Lambda, 
                     ExprTuple, ExprRange, prover)
from proveit.linear_algebra import ScalarMult, TensorProd, VecSum
from proveit.logic import SetMembership, SetNonmembership, CartExp
from proveit.numbers import num
from proveit import a, b, f, i, j, m, n, x, A, K, Q, V


class TensorProdMembership(SetMembership):
    '''
    Defines methods that apply to membership in a TensorProd
    (i.e. membership in a tensor product).
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Side-effects for TensorProd membership.
        '''
        try:
            # If the domain is of the form
            # K^{n_1} ⊗ K^{n_2} ⊗ ... ⊗ K^{n_m}
            # derive that the element is also contained in
            # K^{n_1 + n_2 + ... + K^{n_m}}
            self._get_cart_exps_field_and_exponents()
            # Auto-simplification is turned off when executing
            # side-effects -- turn it back on for this one.
            yield lambda : self.derive_cart_exp_membership(auto_simplify=True)
        except ValueError:
            pass
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
            # might want to change the following to use
            # vec_space_membership = self.element.summand.deduce_in_vec_space()
            # then _V_sub = vec_space_membership.domain
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
    
    @prover
    def derive_cart_exp_membership(self, **defaults_config):
        '''
        If the domain is a tensor product Cartesian exponentials on the
        same field, prove that the element is also a membero of
        the Cartesion exponential of the sum of the exponents.
        Thst is, if the domain is of the form
            K^{n_1} ⊗ K^{n_2} ⊗ ... ⊗ K^{n_m}
        derive that the element is also contained in
            K^{n_1 + n_2 + ... + n_m}
        '''
        from . import tensor_prod_of_cart_exps_within_cart_exp
        _K, _ns = self._get_cart_exps_field_and_exponents()
        _ns = ExprTuple(*_ns)
        _m = _ns.num_elements()
        inclusion = tensor_prod_of_cart_exps_within_cart_exp.instantiate(
                {K:_K, m:_m, n:_ns})
        return inclusion.derive_superset_membership(self.element)
    
    def _get_cart_exps_field_and_exponents(self):
        '''
        Helper for derive_cart_exp_membership.
        '''
        domain = self.domain
        def raise_invalid():
            raise ValueError(
                    "'derive_cart_exp_membership' only applicable on "
                    "a TensorProdMembership where the domain is a "
                    "tensor product of Cartesian exponentials on the "
                    "same field, not %s"%domain)            
        assert isinstance(domain, TensorProd)
        _ns = []
        _K = None
        for domain_factor in domain.factors.entries:
            if isinstance(domain_factor, ExprRange):
                if not isinstance(domain_factor.body, CartExp):
                    raise_invalid()
                factor_K = domain_factor.body.base
                _ns.append(ExprRange(domain_factor.parameter,
                                     domain_factor.body.exponent,
                                     domain_factor.start_index,
                                     domain_factor.end_index,
                                     styles=domain_factor.get_styles()))
            elif isinstance(domain_factor, CartExp):
                factor_K = domain_factor.base
                _ns.append(domain_factor.exponent)
            else:
                raise_invalid()
            if _K is None:
                _K = factor_K
            elif _K != factor_K:
                raise_invalid()
        return _K, _ns
        
                
                
