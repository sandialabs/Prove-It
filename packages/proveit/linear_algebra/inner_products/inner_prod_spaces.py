from proveit import (Function, Literal, Judgment, UnsatisfiedPrerequisites,
                     prover)
from proveit import n, K, H
from proveit.logic import InClass, ClassMembership, InSet
from proveit.linear_algebra.vector_spaces import (
        VecSpaces, containing_vec_space)

class InnerProdSpaces(VecSpaces):
    '''
    An InnerProdSpaces expression denotes the class of inner product
    spaces over a particular field for the InnerProd operation as
    well as VecAdd and ScalarMult operations as with all vector spaces.

    The InnerProdSpaces definition will enforce the operand to be a
    field in order to contain any members (or even define membership).
    This will allow us to use InnerProdSpaces without an explicit 
    constraint on its 'field' operand.
    
    Expression types that may represent inner product spaces may 
    implement a 'deduce_as_inner_prod_space' method to prove its
    membership in the appropriate class of inner product spaces over a 
    provided 'field'.
    
    Expression types that represent a vector in any vector space may 
    implement a 'deduce_in_vec_space' method to prove its membership in
    that space (which may happen to be an inner product space).
    '''
    
    _operator_ = Literal(
            string_format=r'InnerProdSpaces', 
            latex_format=r'\textrm{InnerProdSpaces}',
            theory=__file__)
    
    # Map vector spaces to their known membership(s) within 
    # InnerProdSpaces(K) for some field K. Such a membership relation 
    # is the indication that it is a vector space over the 
    # corresponding field.
    known_vec_spaces_memberships = dict() 
        
    def __init__(self, field, *, styles=None, _operator=None):
        if _operator is None:
            _operator = InnerProdSpaces._operator_
        VecSpaces.__init__(self, field, styles=styles, _operator=_operator)
    
    def membership_object(self, element):
        return InnerProdSpacesMembership(element, self)
    
    @property
    def is_proper_class(self):
        '''
        Vector spaces are proper classes. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

    @staticmethod
    def yield_known_inner_prod_spaces(vec, *, field=None):
        '''
        Given a vector expression, vec, yield any inner product spaces,
        over the specified field, known to contain vec.
        If the field is not specified, VecSpaces.default_field will
        be used, and if a default has not been specified an exception
        will be raised.
        '''
        for vec_space in VecSpaces.yield_known_vec_spaces(vec, field=field):
            if vec_space in InnerProdSpaces.known__vec_space_memberships:
                # This vector space is already known to be an inner
                # product space.
                yield vec_space
            else:
                try:
                    yield deduce_as_inner_prod_space(vec_space)
                except NotImplementedError:
                    # Not known you to prove 'vec_space' is an inner
                    # product space.
                    pass

    @staticmethod
    def known_inner_prod_space(vec, *, field=None):
        '''
        Return the known inner product space of the given vec under the
        specified field (or the default field).
        '''
        field = VecSpaces.get_field(field, may_be_none=True)
        try:
            return next(VecSpaces.yield_known_inner_prod_spaces(
                    vec, field=field))
        except StopIteration:
            # We may not know that 'vec' is in a vector space,
            # but we may be able to deduce it in a straightforward
            # manner provided it has a 'deduce_in_vec_space' method.
            try:
                vec_space = containing_vec_space(vec, field=field)
                # Make sure we can prove vec_space is an inner product
                # space.
                deduce_as_inner_prod_space(vec_space)
                return vec_space                
            except NotImplementedError:
                over_field_msg = "" if field is None else " over %s"%field
                raise UnsatisfiedPrerequisites(
                        "%s is not known to be in an inner product space%s"
                        %(vec, over_field_msg))

    @staticmethod
    def known_inner_prod_spaces(vecs, *, field=None):
        '''
        Return the known vector spaces of the given vecs under the
        specified field (or the default field).
        '''
        # TODO: appropriately handle an ExprRange opernd.
        return [VecSpaces.known_inner_prod_space(operand, field=field)
                for operand in vecs]    
    


class InnerProdSpacesMembership(ClassMembership):
    def __init__(self, element, domain):
        ClassMembership.__init__(self, element, domain)
        if not isinstance(domain, InnerProdSpaces):
            raise TypeError("domain expected to be InnerProdSpaces, not %s"
                            %domain.__class__)
        self.field = domain.field
    
    def side_effects(self, judgment):
        '''
        Prove VecSpaces membership as a side-effect and
        remember known InnerProdSpaces memberships.
        '''
        InnerProdSpaces.known_vec_spaces_memberships.setdefault(
                self.element, set()).add(judgment)
        yield self.derive_vec_spaces_membership
    
    @prover
    def derive_vec_spaces_membership(self, **defaults_config):
        '''
        Derive that the element is a vector space if it is an inner
        product space.
        '''
        from . import inner_prod_space_is_vec_space
        return inner_prod_space_is_vec_space.instantiate(
                {K:self.field, H:self.element})
        
    def conclude(self):
        '''
        Attempt to conclude this membership in a class of inner product
        spaces.
        '''
        return deduce_as_inner_prod_space(self.element)


@prover
def deduce_as_inner_prod_space(expr, *, field=None,
                               **defaults_config):
    '''
    Prove that the given expression is contained in class of inner
    product spaces over some field.
    '''
    from proveit.logic import CartExp
    if field is not None and InClass(expr, InnerProdSpaces(field)).proven():
        # Already known as an appropriate inner product space.
        return InClass(expr, InnerProdSpaces(field)).prove()
    if isinstance(expr, CartExp):
        '''
        For the Cartesian exponentiation of rational, real, or
        complex numbers, we can deduce that it is a member of
        the class of inner product spaces over the corresponding field.
        '''
        from proveit.numbers import Rational, Real, Complex
        from . import (
                rational_vec_set_is_inner_prod_space, 
                real_vec_set_is_inner_prod_space, 
                complex_vec_set_is_inner_prod_space)
        if expr.base == Rational:
            return rational_vec_set_is_inner_prod_space.instantiate(
                    {n:expr.exponent})
        elif expr.base == Real:
            return real_vec_set_is_inner_prod_space.instantiate(
                    {n:expr.exponent})
        elif expr.base == Complex:
            return complex_vec_set_is_inner_prod_space.instantiate(
                    {n:expr.exponent})
        raise NotImplementedError("'deduce_as_inner_prod_space' is not implemented "
                                  "to handle %s"%expr)
    if hasattr(expr, 'deduce_as_inner_prod_space'):
        # If there is a 'deduce_as_inner_prod_space' class method for
        # the expression, try that.
        membership = expr.deduce_as_inner_prod_space()
    if membership is not None:
        InClass.check_proven_class_membership(
                membership, expr, InnerProdSpaces)
        if field is not None and membership.domain.field != field:
            raise ValueError("'deduce_as_inner_prod_space' proved membership "
                             "in inner product spaces over %s, not over "
                             "the requested %s field"
                             %(membership.domain.field, field))
            
        return membership
    raise NotImplementedError(
            "'deduce_as_inner_prod_space' is only implemented when "
            "the element is a CartExp expression or has a "
            "'deduce_as_inner_prod_space' method; %s "
            "does not have such a method"%expr.__class__)
