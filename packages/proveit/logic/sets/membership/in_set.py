from proveit import (Literal, defaults, USE_DEFAULTS,
                     prover, equality_prover, relation_prover)
from proveit.relation import Relation
from proveit.logic.classes import InClass, ClassMembership

class InSet(InClass):
    '''
    Set membership is a special case of class membership, so we'll
    derive from InClass for code re-use.  The operators are distinct
    (though the formatting is the same).
    '''
    # operator of the InSet operation
    _operator_ = Literal(string_format='in', latex_format=r'\in',
                         theory=__file__)

    # map (element, domain) pairs to corresponding InSet expressions
    inset_expressions = dict()

    def __init__(self, element, domain, *, styles=None):
        InSet.inset_expressions[(element, domain)] = self
        InClass.__init__(self, element, domain, operator=InSet._operator_,
                         styles=styles)

    def negated(self):
        '''
        Return the negated membership expression,
        element not in domain.
        '''
        from not_in_set import NotInSet
        return NotInSet(self.element, self.domain)

    @prover
    def deduce_not_in(self, **defaults_config):
        r'''
        Deduce x not in S assuming not(A in S), where self = (x in S).
        '''
        from .not_in_set import NotInSet
        return NotInSet(self.element, self.domain).conclude_as_folded()


class SetMembership(ClassMembership):
    def __init__(self, element, domain):
        '''
        Base class for any 'membership object' returned by a domain's
        'membership_object' method.
        '''
        # The expression represented by this Membership.
        if (element, domain) in InSet.inset_expressions:
            expr = InSet.inset_expressions[(element, domain)]
        else:
            expr = InSet(element, domain)
        ClassMembership.__init__(self, element, domain, expr=expr)
