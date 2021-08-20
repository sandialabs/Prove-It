from proveit import (Literal, defaults, USE_DEFAULTS, equality_prover, 
                     prover, relation_prover)
from proveit import x, S
from proveit.relation import Relation
from proveit.logic.classes import NotInClass, ClassNonmembership


class NotInSet(NotInClass):
    '''
    Set nonmembership is a special case of class nonmembership, so we'll
    derive from NotInClass for code re-use.  The operators are distinct 
    (though the formatting is the same).
    '''
    # operator of the NotInSet operation
    _operator_ = Literal(string_format='not-in', latex_format=r'\notin',
                         theory=__file__)

    # map (element, domain) pairs to corresponding NotInSet expressions
    notinset_expressions = dict()

    def __init__(self, element, domain, *, styles=None):
        NotInSet.notinset_expressions[(element, domain)] = self
        NotInClass.__init__(self, element, domain, operator=NotInSet._operator_,
                          styles=styles)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce and return that this 'not in' statement is in the set
        of BOOLEANS. For example,
        NotInSet(x, {1, 2, 3}).deduce_in_bool()
        returns |- NotInSet(x, {1, 2, 3}) in Bool
        '''
        from . import not_in_set_is_bool
        from proveit import x, S
        return not_in_set_is_bool.instantiate(
                {x: self.element, S: self.domain})

    @prover
    def unfold_not_in(self, **defaults_config):
        r'''
        From (x \notin y), derive and return Not(x \in y).
        For example,
        NotInSet(a, {b, c, d}).unfold_not_in(
                assumptions=[NotInSet(a, {b, c, d})])
        and
        NotInSet(a, {b, c, d}).unfold_not_in(
                assumptions=[NotEquals(a, b), NotEquals(a, c),
                             NotEquals(a, d)])
        both return
        NotInSet(a, {b, c, d}) |- Not (a in {b, c, d}),
        We include the auto_simplify=False to keep the membership
        result inside the Not() from being reduced to False.
        '''
        from . import unfold_not_in_set
        return unfold_not_in_set.instantiate(
            {x: self.element, S: self.domain}, auto_simplify=False)

    def conclude_as_folded(self, assumptions=USE_DEFAULTS):
        '''
        Attempt to conclude x not in S via Not(x in S).
        '''
        from . import fold_not_in_set
        return fold_not_in_set.instantiate(
            {x: self.element, S: self.domain}, assumptions=assumptions)


class SetNonmembership(ClassNonmembership):
    def __init__(self, element, domain):
        '''
        Base class for any 'membership object' returned by a domain's
        'membership_object' method.
        '''
        # The expression represented by this Membership.
        if (element, domain) in NotInSet.notinset_expressions:
            expr = NotInSet.notinset_expressions[(element, domain)]
        else:
            expr = NotInSet(element, domain)
        ClassNonmembership.__init__(self, element, domain, expr=expr)
