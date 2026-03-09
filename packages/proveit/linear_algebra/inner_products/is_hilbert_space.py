from proveit import (Literal, UnsatisfiedPrerequisites,
                     prover, ClassMembership)
from proveit import n
from proveit.numbers import Complex
from .is_inner_prod_space import IsInnerProdSpace

class IsHilbertSpace(ClassMembership):
    '''
    IsHilbertSpace denotes membership in the inner product space over
    the Complex number field.
    '''

    _operator_ = Literal(
            string_format=r'IsHilbertSpace', 
            latex_format=r'\textrm{IsHilbertSpace}',
            theory=__file__)
    
    def __init__(self, space, *, styles=None):
        ClassMembership.__init__(self, IsHilbertSpace._operator_,
                                 space, styles=styles)

    def formatted_class(self, format_type):
        if format_type == 'latex':
            return r'{\rm HilbertSpace}'
        return r'HilbertSpace'

    @property
    def field(self):
        return Complex

    def side_effects(self, judgment):
        '''
        Prove inner product and vector spacememberships as side-effects.
        '''
        yield self.derive_inner_prod_spaces_membership
        yield self.derive_vec_spaces_membership
    
    @prover
    def derive_inner_prod_spaces_membership(self, **defaults_config):
        '''
        Derive that the element is an inner product space over Complex
        numbers from being a Hilbert space.
        '''
        from . import Hspace
        from . import hilbert_space_is_inner_prod_space
        return hilbert_space_is_inner_prod_space.instantiate(
                {Hspace:self.space})

    @prover
    def derive_vec_spaces_membership(self, **defaults_config):
        '''
        Derive that the element is a vector space over Complex
        numbers from being a Hilbert space.
        '''
        from . import Hspace
        from . import hilbert_space_is_vec_space
        return hilbert_space_is_vec_space.instantiate(
                {Hspace:self.space})
    
    def conclude(self):
        '''
        Attempt to conclude this membership in a class of inner product
        spaces.
        '''
        return deduce_as_hilbert_space(self.space)

    @staticmethod
    def yield_known_hilbert_spaces(vec):
        '''
        Given a vector expression, vec, yield any Hilbert spaces
        known to contain vec.
        '''
        from . import HilbertSpaces
        from proveit.linear_algebra import IsVecSpace
        for vec_space in IsVecSpace.yield_known_vec_spaces(vec, field=Complex):
            if IsHilbertSpace(vec_space).proven():
                # This vector space is already known to be an inner
                # product space.
                yield vec_space
            else:
                try:
                    deduce_as_hilbert_space(vec_space)
                    yield vec_space
                except NotImplementedError:
                    # Not known you to prove 'vec_space' is an inner
                    # product space.
                    pass

    @staticmethod
    def known_hilbert_space(vec):
        '''
        Return the known inner product space of the given vec under the
        specified field (or the default field).
        '''
        from proveit.linear_algebra import containing_vec_space
        try:
            return next(IsHilbertSpace.yield_known_hilbert_spaces(vec))
        except StopIteration:
            # We may not know that 'vec' is in a vector space,
            # but we may be able to deduce it in a straightforward
            # manner provided it has a 'deduce_in_vec_space' method.
            try:
                vec_space = containing_vec_space(vec, field=Complex)
                # Make sure we can prove vec_space is an inner product
                # space.
                deduce_as_hilbert_space(vec_space)
                return vec_space                
            except NotImplementedError:
                raise UnsatisfiedPrerequisites(
                        "%s is not known to be in a Hilbert space")

    @staticmethod
    def known_hilbert_spaces(vecs, *, field=None):
        '''
        Return the known vector spaces of the given vecs under the
        specified field (or the default field).
        '''
        # TODO: appropriately handle an ExprRange opernd.
        return [IsHilbertSpace.known_hilbert_space(operand)
                for operand in vecs]    

@prover
def deduce_as_hilbert_space(expr, **defaults_config):
    '''
    Prove that the given expression is contained in class of Hilbert
    spaces over some field.
    '''
    from proveit.logic import CartExp
    from . import HilbertSpaces, hilbert_space_def
    if IsHilbertSpace(expr).proven():
        # Already known as an appropriate vector space.
        return IsHilbertSpaces(expr).prove()
    if isinstance(expr, CartExp):
        '''
        For the Cartesian exponentiation of rational, real, or
        complex numbers, we can deduce that it is a member of
        the class of inner product spaces over the corresponding field.
        '''
        from .import complex_vec_set_is_hilbert_space
        if expr.base == Complex:
            return complex_vec_set_is_hilbert_space.instantiate(
                    {n:expr.exponent})
        raise NotImplementedError(
                "'deduce_as_hilbert_space' is not implemented "
                "to handle %s"%expr)
    if hasattr(expr, 'deduce_as_hilbert_space'):
        # If there is a 'deduce_as_hilbert_space' class method for
        # the expression, try that.
        membership = expr.deduce_as_hilbert_space()
        ClassMembership.check_proven_class_membership(
            membership, expr, IsHilbertSpace._operator_)
        return membership       
    if hasattr(expr, 'deduce_as_inner_prod_space'):
        # If there is a 'deduce_as_inner_prod_space' class method for
        # the expression, try that since a Hilbert space is just
        # an inner product space over the complex number field. 
        membership = expr.deduce_as_inner_prod_space(field=Complex)
        ClassMembership.check_proven_class_membership(
                membership, expr, IsInnerProdSpace._operator_)
        if membership.domain.field == Complex:
            # From membership in the inner product spaces over complex
            # numbers, prove membership in Hilbert spaces via
            # substitution.
            return hilbert_space_def.lhs_substitute(membership)
    raise NotImplementedError(
            "'deduce_as_inner_prod_space' is only implemented when "
            "the element is a CartExp expression or has a "
            "'deduce_as_inner_prod_space' method; %s "
            "does not have such a method"%expr.__class__)
