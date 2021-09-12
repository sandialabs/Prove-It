from proveit import (Function, Literal, Judgment, UnsatisfiedPrerequisites,
                     prover)
from proveit import n
from proveit.logic import InClass, ClassMembership, InSet
from proveit.linear_algebra.vector_spaces import VecSpaces

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
            # We may not know that 'vec' is in an inner product space,
            # but we may be able to deduce it in a straightforward
            # manner provided it has a 'deduce_in_vec_space' method.
            if hasattr(vec, 'deduce_in_vec_space'):
                vec_in_space = vec.deduce_in_vec_space(field=field)
                # Check that vec_in_space has the right form.
                if (not isinstance(vec_in_space, Judgment) or
                        not isinstance(vec_in_space.expr, InSet)):
                    raise TypeError("'deduce_in_vec_space' expected to "
                                    "return an InSet Judgment")
                if vec_in_space.expr.element != vec:
                    raise ValueError("'deduce_in_vec_space' expected to "
                                     "return an InSet Judgment with "
                                     "the 'vec' as the 'element'")
                vec_space = vec_in_space.domain
                # Make sure we can prove vec_space is an inner product
                # space.
                deduce_as_inner_prod_space(vec_space)
                return vec_space
            over_field_msg = "" if field is None else " over %s"%field
            raise UnsatisfiedPrerequisites(
                    "%s is not known to be in a vector space%s"
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
        Remember known InnnerProdSpaces memberships.
        '''
        InnerProdSpaces.known_vec_spaces_memberships.setdefault(
                self.element, set()).add(judgment)
        return # generator yielding nothing
        yield
    
    def conclude(self):
        '''
        Attempt to conclude this membership in a class of inner product
        spaces.
        '''
        return deduce_as_inner_prod_space(self.element)


@prover
def deduce_as_inner_prod_space(expr, **defaults_config):
    '''
    Prove that the given expression is contained in class of inner
    product spaces over some field.
    '''
    from proveit.logic import CartExp
    if isinstance(expr, CartExp):
        '''
        For the Cartesian exponentiation of rational, real, or
        complex numbers, we can deduce that it is a member of
        the class of inner product spaces over the corresponding field.
        '''
        from proveit.numbers import Rational, Real, Complex
        from . import (
                rational_cart_exp_is_inner_prod_space, 
                real_cart_exp_is_inner_prod_space, 
                complex_cart_exp_is_inner_prod_space)
        if expr.base == Rational:
            return rational_cart_exp_is_inner_prod_space.instantiate(
                    {n:expr.exponent})
        elif expr.base == Real:
            return real_cart_exp_is_inner_prod_space.instantiate(
                    {n:expr.exponent})
        elif expr.base == Complex:
            return complex_cart_exp_is_inner_prod_space.instantiate(
                    {n:expr.exponent})
        raise NotImplementedError("'deduce_as_inner_prod_space' is not implemented "
                                  "to handle %s"%expr)
    if hasattr(expr, 'deduce_as_inner_prod_space'):
        # If there is a 'deduce_as_inner_prod_space' class method for
        # the expression, try that.
        membership = expr.deduce_as_inner_prod_space()
        InClass.check_proven_class_membership(
                membership, expr, InnerProdSpaces)
        return membership
    raise NotImplementedError(
            "'deduce_as_inner_prod_space' is only implemented when "
            "the element is a CartExp expression or has a "
            "'deduce_as_inner_prod_space' method; %s "
            "does not have such a method"%expr.__class__)
