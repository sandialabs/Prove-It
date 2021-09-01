from proveit import Operation, Function, Literal
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

    @classmethod
    def yield_known_vec_spaces(self, vec, *, field):
        '''
        Given a vector expression, vec, yield any vector spaces,
        over the specified field, known to contain vec.
        '''
        for membership in InSet.known_memberships[vec]:
            # Check if the membership domain is a vector space over the
            # specified field.
            is_known_vec_space = InClass(membership.domain, 
                                         VecSpaces(field)).proven()
            if not is_known_vec_space:
                if hasattr(membership.domain, 'deduce_as_vec_space'):
                    # See if we can prove that the domain is a vector
                    # space via 'deduce_as_vec_space'.
                    try:
                        membership.domain.deduce_as_vec_space(field=field)
                        # Assume it worked.
                        is_known_vec_space = True
                    except NotImplementedError:
                        pass
            if is_known_vec_space:
                # Match found: vec is a member of a domain
                # that is a vector space over the specified field.
                yield membership.domain

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
            return self.element.deduce_as_vec_space(field=self.field)
        raise NotImplementedError(
                "VecSpacesMembership.conclude is only implemented when "
                "the element has a 'deduce_as_vec_space' method; %s "
                "does not have such a method"%self.element.__class__)
