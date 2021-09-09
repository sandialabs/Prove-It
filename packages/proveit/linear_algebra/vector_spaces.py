from proveit import Function, Literal, Judgment, UnsatisfiedPrerequisites
from proveit.logic import InClass, ClassMembership, InSet

class VecSpaces(Function):
    '''
    A VecSpaces expression denotes the class of vector spaces
    over a particular field for the VecAdd and ScalarMult operations.
    
    The VecSpaces definition will enforce the operand to be a field
    in order to contain any members (or even define membership).
    This will allow us to use VecSpaces without an explicit constraint
    on its 'field' operand.
    
    Expression types that may represent vector spaces may implement a
    'deduce_as_vec_space' method to prove its membership in
    the appropriate class of vector spaces over a provided 'field'.
    '''
    
    _operator_ = Literal(
            string_format=r'VecSpaces', latex_format=r'\textrm{VecSpaces}',
            theory=__file__)

    # A default field may be set for convenience when determining
    # a known vector spaces (see 'yield_known_vec_spaces').
    default_field = None
    
    # Map vector spaces to their known membership(s) within 
    # VecSpaces(K) for some field K. Such a membership relation is the 
    # indication that it is a vector space over the corresponding field.
    known_vec_spaces_memberships = dict() 
        
    def __init__(self, field, *, styles=None):
        Function.__init__(self, VecSpaces._operator_, field, styles=styles)
        self.field = field
    
    def membership_object(self, element):
        return VecSpacesMembership(element, self)
    
    @property
    def is_proper_class(self):
        '''
        Vector spaces are proper classes. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True

    @staticmethod
    def get_field(field=None, *, may_be_none=False):
        '''
        Return the given field if one is provide (not None), or the 
        default_field if one was specified, or raise an excaption.
        '''
        if field is not None:
            return field
        if VecSpaces.default_field is not None:
            return VecSpaces.default_field
        if not may_be_none:
            raise ValueError("A field for vector spaces was not specified "
                             "and VecSpaces.default_field was not set.")

    @staticmethod
    def yield_known_vec_spaces(vec, *, field=None):
        '''
        Given a vector expression, vec, yield any vector spaces,
        over the specified field, known to contain vec.
        If the field is not specified, VecSpaces.default_field will
        be used, and if a default has not been specified an exception
        will be raised.
        '''
        from proveit.logic import SubsetEq
        field = VecSpaces.get_field(field, may_be_none=True)
        if vec not in InSet.known_memberships:
            return # No known memberships to potentially yield.
        for membership in InSet.known_memberships[vec]:
            if not membership.is_applicable():
                # Skip it if it isn't usable under current default
                # assumptions.
                continue 
            # Check if the membership domain is a vector space over the
            # specified field.
            domain = membership.domain
            is_known_vec_space = False
            if (field is None and 
                    domain in VecSpaces.known_vec_spaces_memberships):
                is_known_vec_space = True
            elif (field is not None and
                      InClass(domain, VecSpaces(field)).proven()):
                is_known_vec_space = True
            else:
                if hasattr(domain, 'containing_vec_space'):
                    # See if there is a vector space that contains
                    # 'domain' over the specified field.
                    try:
                        domain = domain.containing_vec_space(field)
                    except NotImplementedError:
                        # Presume that the field and domain are not
                        # a good match and continue on.
                        continue
                    if domain != membership.domain:
                        known_field = VecSpaces.known_field(domain)
                        if field is not None and known_field != field:
                            raise ValueError(
                                    "'containing_vec_space' returned %s "
                                    "which is not known to be a vector "
                                    "spaces over %s"
                                    %(domain, field))
                        # Make sure this new domain contains the
                        # old domain.
                        SubsetEq(membership.domain, domain).prove()
                    is_known_vec_space = True
                elif hasattr(domain, 'deduce_as_vec_space'):
                    # See if we can prove that the domain is a vector
                    # space via 'deduce_as_vec_space'.
                    try:
                        domain_in_vec_space = domain.deduce_as_vec_space()
                        if (not isinstance(domain_in_vec_space, Judgment)
                                or not isinstance(domain_in_vec_space.expr, 
                                                  InClass)
                                or domain_in_vec_space.element != domain
                                or not isinstance(domain_in_vec_space.domain,
                                                  VecSpaces)):
                            raise ValueError(
                                    "'deduce_as_vec_space' was expected to "
                                    "return a proven membership of %s"
                                    "with a class of vector spaces; "
                                    "received %s instead"
                                    %(domain, domain_in_vec_space))
                        is_known_vec_space = True
                    except NotImplementedError:
                        pass
            if is_known_vec_space:
                # Match found: vec is a member of a domain
                # that is a vector space over the specified field.
                yield domain
    
    @staticmethod
    def yield_known_fields(vec_space):
        '''
        Given a vector space, yield its known fields.
        '''
        if vec_space in VecSpaces.known_vec_spaces_memberships:
            judgments = VecSpaces.known_vec_spaces_memberships[vec_space]
            for judgment in judgments:
                yield judgment.expr.domain.field

    @staticmethod
    def known_vec_space(vec, *, field=None):
        '''
        Return the known vector space of the given vec under the
        specified field (or the default field).
        '''
        field = VecSpaces.get_field(field, may_be_none=True)
        try:
            return next(VecSpaces.yield_known_vec_spaces(vec, field=field))
        except StopIteration:
            # We may not know that 'vec' is in a vector space,
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
                if hasattr(vec_space, 'deduce_as_vec_space'):
                    # Be sure to prove that this is a vector space.
                    vec_space.deduce_as_vec_space()
                return vec_space
            over_field_msg = "" if field is None else " over %s"%field
            raise UnsatisfiedPrerequisites(
                    "%s is not known to be in a vector space%s"
                    %(vec, over_field_msg))

    @staticmethod
    def known_vec_spaces(vecs, *, field=None):
        '''
        Return the known vector spaces of the given vecs under the
        specified field (or the default field).
        '''
        # TODO: appropriately handle an ExprRange opernd.
        return [VecSpaces.known_vec_space(operand, field=field)
                for operand in vecs]    
    
    @staticmethod
    def known_field(vec_space):
        '''
        Given a vector space, return any known field.
        '''
        try:
            return next(VecSpaces.yield_known_fields(vec_space))
        except StopIteration:
            raise UnsatisfiedPrerequisites("%s is not a known vector space"
                                           %vec_space)

    


class VecSpacesMembership(ClassMembership):
    def __init__(self, element, domain):
        ClassMembership.__init__(self, element, domain)
        if not isinstance(domain, VecSpaces):
            raise TypeError("domain expected to be VecSpaces, not %s"
                            %domain.__class__)
        self.field = domain.field
    
    def side_effects(self, judgment):
        '''
        Remember known VecSpaces memberships.
        '''
        VecSpaces.known_vec_spaces_memberships.setdefault(
                self.element, set()).add(judgment)
        return # generator yielding nothing
        yield
    
    def conclude(self):
        '''
        Attempt to conclude this membership in a class of vector
        spaces.
        '''
        if hasattr(self.element, 'deduce_as_vec_space'):
            return self.element.deduce_as_vec_space()
        raise NotImplementedError(
                "VecSpacesMembership.conclude is only implemented when "
                "the element has a 'deduce_as_vec_space' method; %s "
                "does not have such a method"%self.element.__class__)
