from proveit import A, Judgment, Literal
from proveit.logic import NotEquals
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

    def not_equals_side_effects(self, judgment):
        '''
        For a judgment or assumption of the form A ≠ EmptySet,
        derive the existential Judgment:

          |- Exists_{x} [x in A]

        (i.e., if A is not empty, there must exist an element in A).
        This side-effect method is called from NotEquals.side_effects().
        '''

        from . import EmptySet
        if not isinstance(judgment, Judgment):
            raise ValueError(
                    "EmptySet.not_equals_side_effects() expecting 'judgment' "
                    f"argument to be Judgment but got {judgment}.")
        if not isinstance(judgment.expr, NotEquals):
            raise ValueError(
                    "EmptySet.not_equals_side_effects() expecting "
                    "'judgment' argument to be an inequality Judgment "
                    f"but got {judgment}.")
        if not isinstance(judgment.rhs, EmptySetLiteral):
            raise ValueError(
                    "EmptySet.not_equals_side_effects() expecting "
                    "'judgment' argument have rhs be EmptySet, "
                    f"but got {judgment.rhs}.")
        from proveit.logic.sets import non_empty_unfolding
        _A_sub = judgment.lhs
        yield (lambda : non_empty_unfolding.instantiate({A:_A_sub}))

