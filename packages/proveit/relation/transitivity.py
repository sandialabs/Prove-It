"""
A TransitiveRelation is a generic base class for binary
relationships that are transitive.  Less than and greater than
relationships are examples (so are subset and superset relationships).
For example, transitivity in the "less than" context means that 
a<b and b<c implies that a<c.  Equality (proveit.logic.Equals) is
special kind of TransitiveRelation that is alsy symmetric; that is,
y=x if x=y.  proveit.logic.Equals is a TransitiveRelation, but
overloads the default methods.  The TransitiveRelation class
provides convenient automation capabilities for performing
a transitive search to conclude a new relation from known relations
using transitivity rules.  To enable this, each TransitiveRelation
needs to track to define knownLeftSides and knownRightSides as
class dictionaries; these will be populated as side effects for
each proven relation (see deriveSideEffects).  Also, the
applyTransitivity method should be appropriately implemented.
The default version handles the case when the "other" relation
is an equality (in which case, substitution may simply be performed).
"""


from proveit import Expression, Operation, OperationSequence
from proveit import defaults, USE_DEFAULTS, KnownTruth, ProofFailure
import itertools

class TransitiveRelation(Operation):
    r'''
    Base class for generic transitive relations.  Examples
    are <, <=, >, >= as well as subset, subseteq, superset,
    and superseteq relations.  proveit.logic.Equals is a special 
    TransitiveRelation which is also symmetric (x=y means that y=x).
    '''
    
    def __init__(self, operator, lhs, rhs):
        Operation.__init__(self,operator, (lhs, rhs))
        self.lhs = lhs
        self.rhs = rhs

    def sideEffects(self, knownTruth):
        '''
        Automatically derive the reversed form of transitive
        relations as side effects (e.g., y > x from x < y).
        Also, store known left sides and known right sides 
        in class member dictionaries: knownLeftSides, knownRightSides
        whilc will enable transitivity searches.
        '''
        if not hasattr(self.__class__, 'knownLeftSides') or not hasattr(self.__class__, 'knownRightSides'):
            raise NotImplementedError("Expressions derived from TransitiveRelation should define 'knownLeftSides' and 'knownRightSides' as class variables")
        self.__class__.knownLeftSides.setdefault(self.lhs, set()).add(knownTruth)
        self.__class__.knownRightSides.setdefault(self.rhs, set()).add(knownTruth)
        return
        yield # makes this a generator as it should be

    def conclude(self, assumptions):
        '''
        Try to conclude the TransitivityRelation using other 
        TransitivityRelations or Equals that are known to be true via transitivity.
        For example, if a<b, b=c, and c<=d are known
        truths (under the given assumptions), we can conclude that
        a<d (under these assumptions).
        '''
        # Use a breadth-first search approach to find the shortest
        # path to get from one end-point to the other.
        try:
            return self.concludeViaTransitivity(assumptions)
        except TransitivityException as e:
            raise TransitivityException(self, assumptions, e.message) # indicate the expression we were trying to prove
        self.prove(assumptions=assumptions, automation=False) # this is just an extra sanity check
        
    def concludeViaTransitivity(self, assumptions=USE_DEFAULTS):
        from proveit.logic import Equals
        assumptions = defaults.checkedAssumptions(assumptions)
        if self.__class__ == Equals: forceStrong = False # "strong" vs "weak" doesn't make sense when the relation is simply equality
        else: forceStrong = (self.__class__ == self.__class__._checkedStrongRelationClass())
        return self.__class__._transitivitySearch(self.lhs, self.rhs, forceStrong=forceStrong, assumptions=assumptions)

    @staticmethod
    def WeakRelationClass():
        raise NotImplementedError("The Expression class for the weak form of the relation (that include equality as a possibility) should be returned")

    @staticmethod
    def StrongRelationClass():
        raise NotImplementedError("The Expression class for the strong form of the relation (that excludes equality as a possibility) should be returned")

    @classmethod
    def _checkedWeakRelationClass(RelationClass):
        from proveit.logic import Equals
        if RelationClass==Equals: return Equals # ("equal to" or "equal to" is just "equal to")
        Relation = RelationClass.WeakRelationClass()
        assert issubclass(Relation, TransitiveRelation), "WeakRelationClass() should return a sub-class of TransitiveRelation"
        return Relation

    @classmethod
    def _checkedStrongRelationClass(RelationClass):
        Relation = RelationClass.StrongRelationClass()
        assert issubclass(Relation, TransitiveRelation), "StrongRelationClass() should return a sub-class of TransitiveRelation"
        return Relation

    @staticmethod
    def SequenceClass():
        raise NotImplementedError("The Expression class for the transitive relation sequence should be returned")

    @classmethod
    def makeSequence(self, *relations):
        Sequence = self.SequenceClass()
        assert issubclass(Sequence, TransitiveSequence), "SequenceClass() should return a sub-class TransitiveSequence"
        operators = [relation.operator for relation in relations]
        operands = [relation.lhs for relation in relations] + [relations[-1].rhs]
        alt_operands = [relations[0].lhs] + [relation.rhs for relation in relations]
        if operands != alt_operands:
            raise TypeError("The relations do not have the expected operands in common to form a sequence")
        return Sequence(operators, operands)
    
    @classmethod
    def sort(RelationClass, items, reorder=True, assumptions=USE_DEFAULTS):
        assumptions = defaults.checkedAssumptions(assumptions)
        if reorder:
            return RelationClass._transitivitySort(items, assumptions=assumptions)
        else:
            return RelationClass._fixedTransitivitySort(items, assumptions=assumptions)
    
    @classmethod
    def insert(RelationClass, sequence, item, assumptions=USE_DEFAULTS):
        assumptions = defaults.checkedAssumptions(assumptions)
        return RelationClass._transitivityInsert(sequence, item, assumptions)
                                
    @classmethod
    def knownRelationsFromLeft(RelationClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, right-hand-side) pairs for this
        transitive relationship (or equality) that involve the given expression on 
        the left side and are known to be true under the given assumptions.
        The strongest known relationships should be yielded first, starting
        with equalities (for inequalities, next is < followed by <=).
        '''
        from proveit.logic import Equals
        # equality relationships are strongest and should come first.
        for (knownTruth, otherExpr) in Equals.knownRelationsFromLeft(expr, assumptionsSet):
            if expr != otherExpr: # exclude reflexive equations -- they don't count
                yield (knownTruth, otherExpr)
        if RelationClass is not Equals:
            # stronger then weaker relations
            for Relation in (RelationClass._checkedStrongRelationClass(), RelationClass._checkedWeakRelationClass()):
                for knownTruth in list(Relation.knownLeftSides.get(expr, [])):
                    if knownTruth.isSufficient(assumptionsSet):
                        yield (knownTruth, knownTruth.rhs)
                
    @classmethod
    def knownRelationsFromRight(RelationClass, expr, assumptionsSet):
        '''
        Yield (KnownTruth, left-hand-side) pairs for this
        transitivie relationship (or equality) that involve the given expression on 
        the right side and are known to be true under the given assumptions.
        The strongest known relationships should be yielded first, starting
        with equalities (for inequalities, next is < followed by <=).
        '''
        from proveit.logic import Equals
        # equality relationships are strongest and should come first.
        for (knownTruth, otherExpr) in Equals.knownRelationsFromRight(expr, assumptionsSet):
            if expr != otherExpr: # exclude reflexive equations -- they don't count
                yield (knownTruth, otherExpr)
        if RelationClass is not Equals:
            # stronger then weaker relations
            for Relation in (RelationClass._checkedStrongRelationClass(), RelationClass._checkedWeakRelationClass()):
                for knownTruth in list(Relation.knownRightSides.get(expr, [])):
                    if knownTruth.isSufficient(assumptionsSet):
                        yield (knownTruth, knownTruth.lhs)
    
    def applyTransitivity(self, other, assumptions=USE_DEFAULTS):
        '''
        Apply transitivity to derive a new relation from 'self' and 'other'.
        For example, from self:a<b, other:b=c, derive a<c.
        This must be implemented for the different types of transitive
        relations.  This default version handles the case where
        'other' is an equality (as in the above example.
        '''
        from proveit.logic import Equals
        from proveit.lambda_map import SubExprRepl
        #print 'apply transitivity', self, other
        assumptions = defaults.checkedAssumptions(assumptions)        
        if isinstance(other,Equals):
            if other.lhs in (self.lhs, self.rhs):
                subrule = other.rhsSubstitute
                commonExpr = other.lhs
            elif other.rhs in (self.lhs, self.rhs):
                subrule = other.lhsSubstitute
                commonExpr = other.rhs
            else:
                raise ValueError("Equality does not involve either side of inequality!")
            if commonExpr == self.lhs:
                # replace the lhs of self with its counterpart from the "other" equality.
                return subrule(SubExprRepl(self).lhs, assumptions=assumptions)
            elif commonExpr == self.rhs:
                # replace the rhs of self with its counterpart from the "other" equality.
                return subrule(SubExprRepl(self).rhs, assumptions=assumptions)
        raise NotImplementedError('Must implement applyTransitivity appropriately for each kind of TransitiveRelation')

    @staticmethod
    def applyTransitivities(chain, assumptions=USE_DEFAULTS):
        '''
        Apply transitvity rules on a list of relations in the given chain
        to proof the relation over the chain end points.
        Each element of the chain must be a KnownTruth object that represents
        a proven relation for which transitivity rules may be applied via
        an 'applyTransitivity' method (such as a KnownTruth for a proven
        Equals statement).  The chain must "connect" in the sense that any
        two neighbors in the chain can be joined vie applyTransitivity.
        The transitivity rule will be applied left to right.
        '''
        assumptions = defaults.checkedAssumptions(assumptions)
        if len(chain) == 0:
            raise TransitivityException(None, assumptions, 'Empty transitivity relation train')
        if not all(isinstance(element, KnownTruth) for element in chain):
            raise TypeError('Expecting chain elements to be KnownTruth objects')
        while len(chain) >= 2:
            first = chain.pop(0)
            second = chain.pop(0)
            chain.insert(0, first.applyTransitivity(second, assumptions=assumptions))
        return chain[0] # we are done
    
    @classmethod
    def _transitivitySearch(RelationClass, leftItem, rightItem, forceStrong, assumptions):
        '''
        Performs a breadth-first, bidirectional (meet in the middle) search attempting
        to prove a relation between leftItem and rightItem according to the RelationClass
        by applying transitivity derivations.
        If successful, the approprate KnownTruth relating these items (in weak or strong
        form as can be determined) is returned; otherwise a TransitivityException is raised.
        If forceStrong is True, only the strong form of the relation is accepted. 
        '''
        assumptions_set = set(assumptions)
        
        # "Chains" map end-points to list of known true relations that get us there
        # by applying transitivity rules.
        # Left chain values will be a list of relations that can take us from
        # relation.lhs to the left chain end-point.
        # Right chain values will be a list of relations that can take us from
        # relation.rhs to the right chain end-point.
        left_chains, right_chains = {leftItem:[]}, {rightItem:[]}
        unexplored_left, unexplored_right = dict(left_chains), dict(right_chains)
        
        # while there is something left to explore on both side
        # (otherwise, we have hit a dead end on one of the sides)
        while len(unexplored_left)>0 and len(unexplored_right)>0:
            # choose the side with the fewest unexplored endpoints.
            # (bias on the left since left-to-right is a common convention)
            if len(unexplored_left) <= len(unexplored_right):
                chains, unexplored_chains = left_chains, unexplored_left
                extensions = lambda endpoint : RelationClass.knownRelationsFromLeft(endpoint, assumptions_set)
                endpoints, other_endpoints = left_chains.keys(), right_chains.keys()
            else:
                chains, unexplored_chains = right_chains, unexplored_right
                extensions = lambda endpoint : RelationClass.knownRelationsFromRight(endpoint, assumptions_set)
                endpoints, other_endpoints = right_chains.keys(), left_chains.keys()
            
            # search for extensions to the unexplored chains and see if any make
            # it to the other side
            new_chains = dict()
            for endpoint, chain in unexplored_chains.iteritems():
                for relation, new_endpoint in extensions(endpoint):
                    if not isinstance(relation, KnownTruth) or not isinstance(new_endpoint, Expression):
                        raise TypeError(str(relation.__class__) + '.knownRelationsFromLeft and ' + str(relation.__class__) \
                                        + '.knownRelationsFromRight should yield (KnownTruth, Expression) pairs')
                    if new_endpoint not in endpoints:
                        # We only care about new chains with new end-points.
                        new_chains[new_endpoint] = chain + [relation]
                        
                        # Do we have an end to end solution?
                        if new_endpoint in other_endpoints:
                            # made it to the other side. we have a solution.
                            # Apply transitivities to generate it and return this new known truth.
                            if chains is left_chains:
                                # bridge the left extension with the reversed right chain
                                full_chain = new_chains[new_endpoint] + list(reversed(right_chains[new_endpoint]))
                            else:
                                # bridge the left chain with the reversed right extension
                                full_chain = left_chains[new_endpoint] + list(reversed(new_chains[new_endpoint]))
                            # This should return a known truth for the desired relation in weak or strong form.
                            relation = TransitiveRelation.applyTransitivities(full_chain, assumptions=assumptions)
                            # If forceStrong is true and the proven relation is weak, continue to keep trying.
                            if not forceStrong or relation.expr.__class__ == RelationClass._checkedStrongRelationClass():
                                return relation
            
            # get the new unexplored chains and update the full set of chains with the new chains
            unexplored_chains.clear()
            unexplored_chains.update({endpoint:chain for endpoint,chain in new_chains.iteritems() \
                                    if endpoint not in chains})
            chains.update(new_chains)
        
        DesiredRelationClass = RelationClass._checkedStrongRelationClass() if forceStrong else  RelationClass._checkedWeakRelationClass()
        raise TransitivityException(DesiredRelationClass(leftItem, rightItem), assumptions, 'No proof found via applying transitivity amongst known proven relations.')
    
    @classmethod
    def _generateSortingRelations(RelationClass, items, assumptionsSet):
        '''
        Generate relations between items via a breadth-first, meet-in-the-middle
        explorations of known relations for the purpose of sorting.  
        Yields ((left-item, right-item), chain) nested
        tuples where the chain is a sequence of relationships going from the left item to
        the right item.  The chains do not extend through other items as these are
        redundant for the purpose of sorting the items.
        '''
        item_set = set(items)
    
        # Map each item to a list of dictionaries mapping end-points to chains
        # of relations going from the item to the end-point.
        frontier_left_chains = {item:{item:[]} for item in items} # going left
        frontier_right_chains = {item:{item:[]} for item in items} # going right
        
        left_endpoint_chains = {item:[[]] for item in items} # map left end-points to chains going from an item to the end-point
        right_endpoint_chains = {item:[[]] for item in items} # map right end-points to chains going from an item to the end-point
        
        # while there are still end-points on the frontier
        while len(frontier_left_chains) + len(frontier_right_chains) > 0:
            # extend to the left or to the right
            for frontier_chains, known_relations, same_endpoint_chains, opposite_endpoint_chains in zip((frontier_left_chains, frontier_right_chains), (RelationClass.knownRelationsFromRight, RelationClass.knownRelationsFromLeft), (left_endpoint_chains, right_endpoint_chains), (right_endpoint_chains, left_endpoint_chains)):
                # extend chains originating from each item
                for item, chains in dict(frontier_chains).iteritems():
                    new_frontier_chains = dict() # new chains from extending the original chains
                    # extend from each frontier end-point
                    for endpoint, chain in chains.iteritems():
                        #print 'starting chain', endpoint, list(chain), ('left' if frontier_chains is frontier_left_chains else 'right')
                        # iterate over each known relation that extend the frontier at the end-point
                        for relation, new_endpoint in known_relations(endpoint, assumptionsSet):
                            if frontier_chains is frontier_left_chains:
                                new_chain = [relation] + chain # extend chain to the left
                            else:
                                new_chain = chain + [relation] # extend chain to the right
                            #print 'extended chain', list(new_chain), 'from', item, 'to', new_endpoint
                            # see if we meet an opposing chain to connect this item with another one (meeting in the middle)
                            if new_endpoint in opposite_endpoint_chains:
                                for meeting_chain in opposite_endpoint_chains[new_endpoint]:
                                    if frontier_chains is frontier_left_chains:
                                        # left-going chain (new_chain) meeting with right-going chain (meeting_chain)
                                        other_item = meeting_chain[0].operands[0] if len(meeting_chain)>0 else new_endpoint
                                        if other_item != item:
                                            yield (other_item, item), meeting_chain + new_chain
                                    else:
                                        # right-going chain (new_chain) meeting with left-going chain (meeting_chain)
                                        other_item = meeting_chain[-1].operands[-1] if len(meeting_chain)>0 else new_endpoint
                                        if other_item != item:
                                            yield (item, other_item), new_chain + meeting_chain
                            # Note, when we make it to another item, we can stop; that other item will come between
                            # the current 'item' and anything beyond.
                            if new_endpoint not in item_set: 
                                # contribute to the 'same_endpoint_chains'
                                same_endpoint_chains.setdefault(new_endpoint, []).append(new_chain)
                                # extend the chain to a new endpoint
                                new_frontier_chains[new_endpoint] = new_chain
                                #print "new frontier", new_endpoint, new_chain
                    if len(new_frontier_chains) > 0:
                        frontier_chains[item] = new_frontier_chains # update the frontier
                    else:
                        # we've exhausted all known relations -- reached the end of the frontier
                        frontier_chains.pop(item)
        
    @classmethod
    def _transitivitySort(RelationClass, items, assumptions):
        '''
        Using the given known transitivity relations (from the left and from the right)
        and the given assumptions, return the items in sorted order according to the transitivity
        relations, proven as a KnownTruth.  If there is not enough information to sort
        the items, a ProofFailure will be raised.  Also, if there are transitivity cycles 
        between items that are not identified as equivalences, a TransitivityException is raised;
        for example, if a <= b, b <= c, and c <= a, then a=b and b=c (or a=c) should be proven
        before calling this sorting routine.
        
        For n items, the performance is O(n log n) when the only known relationships involving the
        items are the necessary, non-redundant relationship between them.  When there are
        extra intermediate relationships, a meet-in-the-middle search is employed (like
        _transitivitySearch except the searches are performed in parallel).  The worst-case
        time complexity, beyond the overhead of meet-in-the-middle searches for extra intermediate
        relationships, is O(n^2 log n) which can occur when the n^2 relationships between the items
        are all (or mostly) known.
        '''
        from proveit.logic import Equals
        
        # This is different than the usual sorting algorithms because there is no control
        # over the known relationships that are provided (they don't come on demand).
        # The efficiency will depend upon what relationships are known; it is best
        # to have a complete but not over-complete set of relationships.
            
        # store relation chains between pairs of items
        item_pair_chains = dict() # (left-item, right-item): chain
        
        # When there are known equivalences, this will map each item
        # of an equivalent set to the full equivalent set.
        eq_sets = {item:{item} for item in items}
        
        left_partners = dict()
        right_partners = dict()
        
        left_most_candidates = set(items)
        
        def yield_left_most(item):
            items_to_process = {item}
            while len(items_to_process) > 0:
                for item in items_to_process:
                    if item in left_partners:
                        items_to_process.update(left_partners[item])
                    else:
                        yield item # end of the line
        
        sorted_items = []
        remaining_items = set(items) # items we have left to sort
        
        for (left_item, right_item), chain in RelationClass._generateSortingRelations(items, assumptions):
            #print left_item, right_item, list(chain)
            if (left_item, right_item) in item_pair_chains:
                # Just use the first chain of relations.
                # If the relation is an equality between the items, that should come first.
                continue 
                
            # add new item partnership to item_pair_chains
            item_pair_chains[(left_item, right_item)] = chain
    
            # If the left and right items are equal, record the equivalence.
            if all(relation.operator==Equals._operator_ for relation in chain):
                eq_set = eq_sets[left_item] | eq_sets[right_item] # join equivalent sets
                for item in eq_set: eq_sets[item] = eq_set # make all the equivalent items point to the same equivalence set
                eq_candidates = left_most_candidates.intersection(eq_set)
                # only keep one of the left-most candidates (an arbitrarily chosen representative)
                if len(eq_candidates) > 1: left_most_candidates.difference_update(list(eq_candidates)[1:])
            else:
                # add new item partnership to left_partners, and right_partners
                left_partners.setdefault(right_item, set()).add(left_item)
                right_partners.setdefault(left_item, set()).add(right_item)                
                # see if we can eliminate any left-most candidates
                eq_right_items = eq_sets[right_item]
                if not left_most_candidates.isdisjoint(eq_right_items):
                    # Assume all cycles are accounted for via equivalences;
                    # otherwise we'll catch it at some point an throw an exception.
                    # Remove all items equivalent to the right item from the left-most candidates
                    # because there is something to the left of it now.
                    left_most_candidates.difference_update(eq_right_items)
                    if len(left_most_candidates)==0:
                        raise TransitivityException(None, assumptions, "Transitivity cycle detected implying equalities; must prove equalities before sorting items: " + str(items))
            
            while len(left_most_candidates)==1:
                # We have one uncontested left-most candidate assuming no cycles outside of equivalence sets
                # (with such cycles, we'll catch them eventually and raise an exception).
                left_most = left_most_candidates.pop()
                sorted_items.append(left_most)
                #print 'left_most', left_most
                
                # note that eq_sets[left_most] should not be extended later because all of the items must
                # determine that they are either to the right of this "left-most" or equal to it before we got here.
                remaining_items.difference_update(eq_sets[left_most]) 
                
                if left_most not in right_partners: 
                    break # nothing known to be on the right of the left-most item; done or need more relations.
                
                # Remove links to the left-most item so we can focus on the next left-most item.
                for right_partner in right_partners[left_most]:
                    left_partners[right_partner].difference_update(eq_sets[left_most])
                
                # Determine the next left-most item candidates based upon
                # what items are rightward from the one that we taken out.
                to_process = set(right_partners[left_most])
                #print to_process
                already_processed = set()
                
                # used to make sure this is an O(n^2 log n) algorithm in the worst case
                processing_everything = (len(to_process)==len(remaining_items))
                num_to_process_insertions = len(to_process) # number of items being inserted into the to_process set
                
                while len(to_process) > 0:
                    next_candidate = to_process.pop()
                    #print 'next_candidate', next_candidate
                    if next_candidate in already_processed: 
                        continue #  we've dealt with that one already
                    left_most_candidates.add(next_candidate) # add as a candidate (may be temporary)
                    eq_next_candidates = eq_sets[next_candidate]
                    for eq_next_candidate in eq_next_candidates:
                        #print 'eq_next_candidate', eq_next_candidate
                        # process the item(s) to the left of 'next_candidate' (or any of the equivalent items)
                        candidate_left_partners = left_partners[eq_next_candidate] if eq_next_candidate in left_partners else []        
                        #print 'candidate_left_partners', candidate_left_partners
                        if not processing_everything: # don't bother updating to_process if we are already processing everything
                            num_to_process_insertions += len(candidate_left_partners)
                            if num_to_process_insertions > len(remaining_items):
                                # Since we're already going through the work of inserting as many items into to_process as
                                # there are items remaining, we might as well process everything to guarantee a bound on 
                                # the worst-case time complexity, avoiding any more insertions in the future.
                                to_process.update(remaining_items) # some of these may already have been processed, but that's okay
                                processing_everything = True
                            else:
                                # more to process for considering left candidates
                                to_process.update(candidate_left_partners) 
                        if len(candidate_left_partners) > 0:
                            # remove the next_candidate (and equivalent items) as a left-most candidate 
                            # because there are one or more items to the left of it.
                            left_most_candidates.difference_update(eq_next_candidates)
                    already_processed.update(eq_next_candidates)
                
                if len(left_most_candidates)==0:
                    raise TransitivityException(None, assumptions, "Transitivity cycle detected implying equalities; must prove equalities before sorting items: " + str(items))
                    
                # Note that we may end up with multiple left-most candidates in which case
                # more links are needed.
            if len(remaining_items)==0: break
                
        if len(left_most_candidates) > 0:
            raise TransitivityException(None, assumptions, "Insufficient known transitive relations to sort the provided items: " + str(items))
        
        orig_order = {item:k for k, item in enumerate(items)}    
        sorted_items = sum([sorted(eq_sets[item], key=lambda it:orig_order[it]) for item in sorted_items], [])
        relations = []
        for item1, item2 in zip(sorted_items[:-1], sorted_items[1:]):
            if (item1, item2) not in item_pair_chains:
                # If may not have the chain for these specific items, but
                # we should have it for something equivalent to each of the items.
                for eq_item1, eq_item2 in itertools.product(eq_sets[item1], eq_sets[item2]):
                    if (eq_item1, eq_item2) in item_pair_chains:
                        # if item1 and eq_item1 are not identical expressions, prove that they are logically equal.
                        prepend = [Equals(item1, eq_item1).prove(assumptions)] if item1 != eq_item1 else [] 
                        # if item2 and eq_item2 are not identical expressions, prove that they are logically equal.
                        append = [Equals(eq_item2, item2).prove(assumptions)] if item2 != eq_item2 else []
                        # make the (item1, item2) chain by prepending/appending necessary equalities to the (eq_item1, eq_item2) chain
                        item_pair_chains[(item1, item2)] = prepend + item_pair_chains[(eq_item1, eq_item2)] + append
            relations.append(TransitiveRelation.applyTransitivities(item_pair_chains[(item1, item2)], assumptions))
        if len(relations)==1:
            return relations[0]
        return RelationClass.makeSequence(*relations)
    
    @classmethod
    def _fixedTransitivitySort(RelationClass, items, assumptions):
        '''
        Check that the given items are in sorted order, returning the sorted
        sequence if they are or raising a TransitivityException if they are not.
        '''
        itemsList = list(items) # in case the items are a non-indexable iterable
        relations = []
        for item1, item2 in zip(itemsList[:-1], itemsList[1:]):
            relations.append(RelationClass._transitivitySearch(item1, item2, forceStrong=False, assumptions=assumptions))
        return RelationClass.applyTransitivities(relations)
    
    @classmethod
    def _transitivityInsert(RelationClass, sequence, item, assumptions):
        '''
        Under the given assumptions, insert 'item' into the given sorted sequence (e.g., that had
        been returned from a call to transitivitySort).
        '''
        # generate relations between any of the sorted sequence operands and the "item" to insert,
        # using a meet in the middle strategy to find out where the item fits.
        items = list(sequence.operands) + [item]
        for (left_item, right_item), chain in RelationClass._generateSortingRelations(items, assumptions):
            if item == left_item:
                right_item_idx = items.index(right_item)
                inserting_relations = []
                if right_item_idx > 0:
                    inserting_relations.append(RelationClass._transitivitySearch(items[right_item_idx-1], item, forceStrong=False, assumptions=assumptions))
                inserting_relations.append(TransitiveRelation.applyTransitivities(chain, assumptions))
                return RelationClass.Sequence(sequence.relations[:right_item_idx-1] + inserting_relations + sequence.relations[right_item_idx:])
            elif item == right_item:
                left_item_idx = items.index(left_item)
                inserting_relations = [TransitiveRelation.applyTransitivities(chain, assumptions)]
                if left_item_idx < len(sequence.operands)-1:
                   inserting_relations.append(RelationClass._transitivitySearch(item, items[left_item_idx+1], forceStrong=False, assumptions=assumptions))
                return RelationClass.Sequence(sequence.relations[:left_item_idx] + inserting_relations + sequence.relations[left_item_idx+1:])        

class TransitiveSequence(OperationSequence):
    '''
    Base clase for Operation Expressions that represent a sequence of transitive relationships.
    For example, w < x = y <= z.  As shown in this example, the relations may include weak, 
    strong, and/or equality.  It may not mix different types of relations.  The type of relation
    is dictated by the RelationClass() class method defined in the derived class.
    '''
    
    def __init__(self, operators, operands):
        from proveit.logic import Equals
        if len(operators) < 2:
            raise ValueError("Do not use a TransitiveSequence for fewer than two relationship (it is unnecessary)")
        Relation = self.__class__.RelationClass()
        assert issubclass(Relation, TransitiveRelation), "The Relation class of a TransitiveSequence should be a TransitiveRelation"
        relation_operators = (Relation.WeakRelationClass()._operator_, Relation.StrongRelationClass()._operator_, Equals._operator_)
        for operator in operators:
            if operator not in relation_operators:
                raise TypeError("Operators of TransitiveSequence should be %s, %s, or %s"%tuple(str(relation_operator) for relation_operator in relation_operators))
        Operation.__init__(self, operators, operands)
    
    @classmethod
    def RelationClass(SequenceClass):
        raise NotImplementedError("Must identify the Relation class for the sequence which should be a TransitiveRelation class")

class TransitivityException(ProofFailure):
    def __init__(self, expr, assumptions, message):
        ProofFailure.__init__(self, expr, assumptions, message)
        