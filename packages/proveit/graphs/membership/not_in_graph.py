from proveit import (Literal, defaults, USE_DEFAULTS, equality_prover, 
                     ProofFailure, prover, relation_prover)
from proveit import x, G
from proveit.relation import Relation
from proveit.logic.classes import NotInClass, ClassNonmembership

# UNDER CONSTRUCTION, ADAPTING FROM InSet beginning 4/16/2025


class NotInGraph(NotInClass):
    '''
    Graph non-membership is a special case of class nonmembership,
    so we derive from NotInClass for code re-use.  The operators are
    distinct (though the formatting is the same).
    '''
    # operator of the NotInSet operation
    _operator_ = Literal(string_format='not-in', latex_format=r'\notin',
                         theory=__file__)

    # map (element, domain) pairs to corresponding NotInGraph exprs
    notingraph_expressions = dict()

    def __init__(self, element, domain, *, styles=None):
        NotInGraph.notingraph_expressions[(element, domain)] = self
        NotInClass.__init__(
                self, element, domain, operator=NotInGraph._operator_,
                styles=styles)

    @relation_prover
    def deduce_in_bool(self, **defaults_config):
        '''
        Deduce and return that this 'not in' statement is in the set
        of BOOLEANS. For example, NotInGraph(x, G(V,E)).deduce_in_bool()
        returns:
                   |- NotInGraph(x, G(V,E)) in Bool.

        '''
        from . import not_in_graph_is_bool
        return not_in_graph_is_bool.instantiate(
                {x: self.element, G: self.domain})

    @prover
    def unfold(self, **defaults_config):
        r'''
        From NotInGraph(x, G), derive and return Not(InGraph(x, G)).
        For example,

            NotInGraph(a, G(V, E)).unfold_not_in(
                assumptions=[NotInGraph(a, G(V, E))])
        returns

            NotInGraph(a, G(V, E)) |- Not (a in G(V, E)).

        We include the auto_simplify=False to keep the membership
        result inside the Not() from being reduced to False.
        '''
        from . import unfold_not_in_graph
        return unfold_not_in_graph.instantiate(
            {x: self.element, G: self.domain}, auto_simplify=False)

    # A placeholder from the NotInSet class; delaying for now
    # come back to this after subgraphs are defined
    # def _readily_provable(self):
    #     '''
    #     This membership is readily provable if the membership
    #     object indicates that it is readily provable or there is a 
    #     known as-strong membership (with known equal elements and the
    #     domain a subset of the desired domain).
    #     '''
    #     if NotInClass._readily_provable(self):
    #         return True
    #     if self.as_strong_known_nonmembership() is not None:
    #         return True
    #     return False

    # A placeholder from the NotInSet class; delaying for now
    # @prover
    # def conclude(self, **defaults_config):
    #     '''
    #     Attempt to conclude that the element is not in the domain. 
    #     First see if the corresponding membership has been disproven. 
    #     Then see if there is a as-strong known nonmembership to use.  
    #     If not, use the NotInClass conclude strategies (which uses the
    #     Relation conclude strategies that simplify both sides and then 
    #     uses the domain-specific conclude method of the membership
    #     object as a last resort).
    #     '''
    #     # Has the membership been disproven?
    #     if self.negated().disproven(): # don't use readily_disprovable
    #         return self.conclude_as_folded()
        
    #     # See if the element, or something known to be equal to
    #     # the element, is known to be a nonmember of the domain or a 
    #     # superset of the domain.
    #     as_strong_nonmembership = self.as_strong_known_nonmembership()
    #     if as_strong_nonmembership is not None:
    #         return self.conclude_from_as_strong_nonmembership(
    #                 as_strong_nonmembership)
    #     return NotInClass.conclude(self)

    @prover
    def conclude_as_folded(self, **defaults_config):
        '''
        Attempt to conclude x not in G via Not(x in G).
        '''
        from . import fold_not_in_graph
        return fold_not_in_graph.instantiate(
            {x: self.element, G: self.domain})

    @prover
    def conclude_negation(self, **defaults_config):
        '''
        Attempt to conclude the negation of nonmembership via
        proving membership.
        '''
        from . import double_negated_membership
        return double_negated_membership.instantiate(
                {x:self.element, G:self.domain})

    # A placeholder from the NotInSet class; delaying for now
    # come back to this after subgraphs are defined
    # @prover
    # def conclude_from_as_strong_nonmembership(
    #         self, as_strong_nonmembership, **defaults_config):
    #     '''
    #     Conclude from a nonmembership with an equal element and a 
    #     domain that is a superset of the desired domain.
    #     '''
    #     from proveit.logic import Equals, SubsetEq
    #     elem_sub = as_strong_nonmembership.element
    #     if as_strong_nonmembership.domain == self.domain:
    #         elem_sub_notin_domain = as_strong_nonmembership
    #     else:
    #         eq_rel = Equals(as_strong_nonmembership.domain, self.domain)
    #         if eq_rel.readily_provable():
    #             # domains are equal -- just substitute the domain.
    #             elem_sub_notin_domain = eq_rel.sub_right_side_into(
    #                     as_strong_nonmembership.inner_expr().domain)
    #         else:
    #             # S is a subset of R, so now we can prove 
    #             # x not in S.
    #             sub_rel = SubsetEq(self.domain, as_strong_nonmembership.domain)
    #             try:
    #                 sub_rel.prove()
    #             except ProofFailure:
    #                 # May have been blocked to avoid infinite
    #                 # recursion.
    #                 return NotInClass.conclude(self)
    #             elem_sub_notin_domain = sub_rel.derive_subset_nonmembership(
    #                     elem_sub)
    #     if elem_sub == self.element:
    #         return elem_sub_notin_domain # done
    #     # Just need to sub in the element for _elem_sub.
    #     Equals(elem_sub, self.element).conclude_via_transitivity()
    #     return elem_sub_notin_domain.inner_expr().element.substitute(
    #             self.element)

    # A placeholder from the NotInSet class; delaying for now
    # come back to this after subgraphs are defined
    # def as_strong_known_nonmembership(self):
    #     '''
    #     If there is a known nonmembership that is as strong as this 
    #     one, where the element is equal to this one's element and the 
    #     domain is a subset of this one's domain, return this
    #     as-strong known membership.  Otherwise, return None.
    #     '''
    #     from proveit.logic import Equals, SubsetEq
    #     known_nonmemberships = list(
    #             NotInClass.yield_known_nonmemberships(self.element))
    #     # First see of there is a known nonmembership with the same domain.
    #     for known_nonmembership in known_nonmemberships:
    #         if known_nonmembership.domain == self.domain:
    #             # this is the best to use; we are done
    #             return known_nonmembership
    #     # Next see of there is a known nonmembership with a domain
    #     # readily provable to be equal to this domain.
    #     for known_nonmembership in known_nonmemberships:
    #         eq_rel = Equals(known_nonmembership.domain, self.domain)
    #         if eq_rel.readily_provable():
    #             return known_nonmembership
    #     # Finaly see of there is a known nonmembership with a domain
    #     # readily provable to be a superset of to this domain.
    #     for known_nonmembership in known_nonmemberships:
    #         sub_rel = SubsetEq(self.domain, known_nonmembership.domain)
    #         if sub_rel.readily_provable():
    #             return known_nonmembership
    #     return None # No match found.

class GraphNonmembership(ClassNonmembership):
    def __init__(self, element, domain):
        '''
        Base class for any 'non-membership object' returned by a
        domain's 'non-membership_object' method.
        '''
        # The expression represented by this Non-Membership.
        if (element, domain) in NotInGraph.notingraph_expressions:
            expr = NotInGraph.notingraph_expressions[(element, domain)]
        else:
            expr = NotInGraph(element, domain)
        ClassNonmembership.__init__(self, element, domain, expr=expr)
