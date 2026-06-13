from proveit import Literal
from proveit.logic.irreducible_value import IrreducibleValue


class EmptySetLiteral(Literal, IrreducibleValue):
    '''
    EmptySet represents the standard empty set, which has no elements.
    EmptySet is then defined in the logic/sets common notebook as
    EmptySet = EmptySetLiteral(), so one can import and use 'EmptySet'
    itself.
    '''

    def __init__(self, *, styles=None):
        Literal.__init__(
            self, string_format='emptyset', latex_format=r'\emptyset',
            styles=styles)

    def membership_object(self, element):
        from .empty_set_membership import EmptySetMembership
        return EmptySetMembership(element, self)

    def nonmembership_object(self, element):
        from .empty_set_membership import EmptySetNonmembership
        return EmptySetNonmembership(element, self)
