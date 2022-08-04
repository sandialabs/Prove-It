from proveit import (Literal, defaults, USE_DEFAULTS, equality_prover, 
                     ProofFailure, prover, relation_prover)
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

    @prover
    def conclude(self, **defaults_config):
        '''
        Attempt to conclude that the element is not in the domain. 
        First see if the corresponding membership has been disproven. 
        Then see if there is a stronger known nonmembership to use.  
        If not, use the NotInClass conclude strategies (which uses the
        Relation conclude strategies that simplify both sides and then 
        uses the domain-specific conclude method of the membership
        object as a last resort).
        '''
        from proveit.logic import Equals, SubsetEq

        # Has the membership been disproven?
        if self.negated().disproven(): # don't use readily_disprovable
            return self.conclude_as_folded()
        
        # See if the element, or something known to be equal to
        # the element, is known to be a nonmember of the domain or a 
        # superset of the domain.
        stronger_nonmembership = self.stronger_known_nonmembership()
        if stronger_nonmembership is not None:
            elem_sub = stronger_nonmembership.element
            if stronger_nonmembership.domain == self.domain:
                elem_sub_notin_domain = stronger_nonmembership
            else:
                eq_rel = Equals(stronger_nonmembership.domain, self.domain)
                if eq_rel.readily_provable():
                    # domains are equal -- just substitute the domain.
                    elem_sub_notin_domain = eq_rel.sub_right_side_into(
                            stronger_nonmembership.inner_expr().domain)
                else:
                    # S is a subset of R, so now we can prove 
                    # x not in S.
                    sub_rel = SubsetEq(self.domain, stronger_nonmembership.domain)
                    try:
                        sub_rel.prove()
                    except ProofFailure:
                        # May have been blocked to avoid infinite
                        # recursion.
                        return NotInClass.conclude(self)
                    elem_sub_notin_domain = sub_rel.derive_subset_nonmembership(
                            elem_sub)
            if elem_sub == self.element:
                return elem_sub_notin_domain # done
            # Just need to sub in the element for _elem_sub.
            Equals(elem_sub, self.element).conclude_via_transitivity()
            return elem_sub_notin_domain.inner_expr().element.substitute(
                    self.element)
        return NotInClass.conclude(self)

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Attempt to conclude x not in S via Not(x in S).
        '''
        from . import fold_not_in_set
        return fold_not_in_set.instantiate(
            {x: self.element, S: self.domain})

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Attempt to conclude the negation of nonmembership via
        proving membership.
        '''
        from . import double_negated_membership
        return double_negated_membership.instantiate(
                {x:self.element, S:self.domain})

    def stronger_known_nonmembership(self):
        '''
        If there is a known nonmembership that is stronger than this 
        one, where the element is equal to this one's element and the 
        domain is a subset of this one's domain, return this
        stronger known membership.  Otherwise, return None.
        '''
        from proveit.logic import Equals, SubsetEq
        for elem_sub in Equals.yield_known_equal_expressions(self.element):
            eq_nonmembership = None # nonmembership in an equal domain
            superset_nonmembership = None # nonmembership in a superset
            for known_nonmembership in (
                    NotInClass.yield_known_nonmemberships(elem_sub)):
                eq_rel = Equals(known_nonmembership.domain, self.domain)
                sub_rel = SubsetEq(self.domain, known_nonmembership.domain)
                if known_nonmembership.domain == self.domain:
                    # this is the best to use; we are done
                    return known_nonmembership
                elif eq_rel.readily_provable():
                    eq_nonmembership = known_nonmembership
                elif sub_rel.readily_provable():
                    superset_nonmembership = known_nonmembership
            if eq_nonmembership is not None:
                return eq_nonmembership
            elif superset_nonmembership is not None:
                return superset_nonmembership
        return None # No match found.

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
