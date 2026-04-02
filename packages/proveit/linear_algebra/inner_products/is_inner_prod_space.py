from proveit import (Literal, UnsatisfiedPrerequisites,
                     prover, ClassMembership)
from proveit import n, K, H
from proveit.linear_algebra.is_vector_space import (
        IsVecSpace, containing_vec_space)

class IsInnerProdSpace(ClassMembership):
    '''
    IsInnerProdSpace denotes membership in the inner product space over
    a given field.  The InnerProd operation on vectors of this inner
    product space will evaluate to a member of this field, and the field
    denotes the type of scalars for ScalarMult.

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
    
    def __init__(self, space, field, *, styles=None):
        ClassMembership.__init__(self, IsInnerProdSpace._operator_, 
                                 space, field, styles=styles)
        self.space = space
        self.field = field

    def formatted_class(self, format_type):
        formatted_field = self.field.formatted(format_type, fence=False)
        if format_type == 'latex':
            return r'{\rm InnerProdSpace}(%s)'%formatted_field
        return r'InnerProdSpace(%s)'%formatted_field

    def incidentals(self, judgment):
        '''
        Prove vector space membership as a side-effect.
        '''
        yield self.derive_vec_spaces_membership
    
    @prover
    def derive_vec_spaces_membership(self, **defaults_config):
        '''
        Derive that the element is a vector space if it is an inner
        product space.
        '''
        from . import inner_prod_space_is_vec_space
        return inner_prod_space_is_vec_space.instantiate(
                {K:self.field, H:self.space})

    @prover
    def conclude(self, **defaults_config): 
        '''
        Attempt to conclude this membership in a class of inner product
        spaces.
        '''
        return deduce_as_inner_prod_space(self.space)

    @staticmethod
    def yield_known_inner_prod_spaces(vec, *, field=None):
        '''
        Given a vector expression, vec, yield any inner product spaces,
        over the specified field, known to contain vec.
        If the field is not specified, VecSpaces.default_field will
        be used, and if a default has not been specified an exception
        will be raised.
        '''
        for vec_space in IsVecSpace.yield_known_vec_spaces(vec, field=field):
            if (field is None and IsInnerProdSpace.has_known_membership(
                    vec_space)):
                yield vec_space
            elif field is not None and (
                    IsInnerProdSpace(vec_space, field).proven()):
                yield vec_space
            else:
                try:
                    deduce_as_inner_prod_space(vec_space)
                    yield vec_space
                except NotImplementedError:
                    # Not known how to prove 'vec_space' is an inner
                    # product space.
                    pass

    @staticmethod
    def known_inner_prod_space(vec, *, field=None):
        '''
        Return the known inner product space of the given vec under the
        specified field (or the default field).
        '''
        field = IsVecSpace.get_field(field, may_be_none=True)
        try:
            return next(IsVecSpace.yield_known_inner_prod_spaces(
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
        return [IsVecSpace.known_inner_prod_space(operand, field=field)
                for operand in vecs]    
    
    @staticmethod
    def yield_readily_provable_inner_prod_spaces(vec_or_vecs, *, field=None):
        '''
        For the given list vec_or_vecs of vectors, yield the set of
        known or readily provable inner product spaces (i.e. the vector
        spaces equipped with an inner product) which the vectors have
        in common.
        '''
        from proveit import Expression, ExprTuple
        if (isinstance(vec_or_vecs, Expression)
            and not isinstance(vec_or_vecs, ExprTuple)):
            # we have a single vector to consider
            for space in IsInnerProdSpace.yield_known_inner_prod_spaces(
                    vec_or_vecs, field=field):
                yield space
        else:
            # we have a list of vectors
            list_of_space_sets = []
            for vec in vec_or_vecs:
                spaces = set()
                for space in (IsInnerProdSpace.
                              yield_readily_provable_inner_prod_spaces(
                              vec, field=field)):
                    spaces.add(space)
                list_of_space_sets.append(spaces)

            # e.g. list_of_space_sets = [{C^3}, {C^3, R^3}, {C^3}]
            space_intersection = set.intersection(*list_of_space_sets)
            for space in space_intersection:
                yield space

@prover
def deduce_as_inner_prod_space(expr, *, field=None,
                               **defaults_config):
    '''
    Prove that the given expression is contained in class of inner
    product spaces over some field.
    '''
    from proveit.logic import CartExp
    if field is not None and IsInnerProdSpace(expr, field).proven():
        # Already known as an appropriate inner product space.
        return IsInnerProdSpace(expr, field).prove()
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
            ClassMembership.check_proven_class_membership(
                membership, expr, IsInnerProdSpace._operator_)
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
