from proveit import ExprTuple, prover, relation_prover, equality_prover
from proveit import m, x, S
from proveit.logic import SetMembership

class CartExpMembership(SetMembership):
    '''
    Defines methods that apply to InSet(element, CartExp(S, n)) objects
    via InSet.__getattr__ which calls CartExp.membership_object(element)
    to return a CartExpMembership object.
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Yield side-effect methods to try when the element is proven to
        be in a CartExp set.
        '''
        yield self.unfold

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to deduce that the given element is in the CartExp set.
        '''
        element = self.element
        if hasattr(element, 'deduce_in_vec_space'):
            '''
            CartExp may be used to denote a vector space (if the base
            set is a field).  If the element has a 'deduce_in_vec_space'
            method, presume that this is the way we should try to
            conclude that the element is in the CartExp set.
            '''
            return element.deduce_in_vec_space(vec_space=self.domain,
                                               field=self.domain.base)
        # If nothing else is applicable, we can try to use 'fold'.
        return self.fold()

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        '''
        Prove [(element in Boolean) = 
                [(element = TRUE) or (element = FALSE)].
        '''
        from . import (cart_exp_abstract_membership_def, 
                       cart_exp_explicit_membership_def)
        _S = self.domain.base
        _m = self.domain.exponent
        _x = self.element
        if isinstance(self.element, ExprTuple):
            #  use the 'explicit' definition for an ExprTuple element
            return cart_exp_explicit_membership_def.instantiate(
                    {m: _m, x: _x, S: _S})
        else:
            # use the 'abstract' unfolding otherwise
            return cart_exp_abstract_membership_def.instantiate(
                    {m: _m, x: _x, S: _S})

    @prover
    def unfold(self, **defaults_config):
        '''
        Prove, for example, (x_1 in S) and ... and (x_m in S) 
        from (x_1, ..., x_m) in S, if the element is an ExprTuple.
        Derive, for example x in (S × ... m repeats ... × S) from x in S
        otherwise.
        '''
        from . import cart_exp_unfold_abstract, cart_exp_unfold_explicit
        _S = self.domain.base
        _m = self.domain.exponent
        _x = self.element
        if isinstance(self.element, ExprTuple):
            #  use the 'explicit' unfolding for an ExprTuple element
            return cart_exp_unfold_explicit.instantiate(
                    {m: _m, x: _x, S: _S}, auto_simplify=False)
        else:
            # use the 'abstract' unfolding otherwise
            _x 
            return cart_exp_unfold_abstract.instantiate(
                    {m: _m, x: _x, S: _S}, auto_simplify=False)

    @prover
    def fold(self, **defaults_config):
        '''
        Prove, for example, (x_1, ..., x_m) in S^m from
        (x_1 in S) and ... and (x_m in S), if the element is an 
        ExprTuple.
        Derive, for example, x in S^m from 
        x in (S × ... m repeats ... × S) otherwise.
        '''
        from . import cart_exp_fold_abstract, cart_exp_fold_explicit
        _S = self.domain.base
        _m = self.domain.exponent
        _x = self.element
        if isinstance(self.element, ExprTuple):
            #  use the 'explicit' unfolding for an ExprTuple element
            return cart_exp_fold_explicit.instantiate(
                    {m: _m, x: _x, S: _S})
        else:
            # use the 'abstract' unfolding otherwise
            _x 
            return cart_exp_fold_abstract.instantiate(
                    {m: _m, x: _x, S: _S})

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Prove, for example, (x in S^m) in bool, provided that
        m is a positive whole number and S is known to be a set
        (membership in S is always boolean).
        '''
        from . import in_cart_exp_is_bool
        _S = self.domain.base
        _m = self.domain.exponent
        _x = self.element
        return in_cart_exp_is_bool.instantiate({m: _m, x: _x, S: _S})
