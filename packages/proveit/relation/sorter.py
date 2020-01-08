import itertools
from collections import deque
from proveit import defaults, USE_DEFAULTS

class TransitivitySorter:
    '''
    The TransitivitySorter is an iterator class that yields 
    Expression items in sorted order w.r.t a TransitivityRelation
    class and according to the given assumptions.  New items may be
    added on the fly under the promise that the new item is
    "beyond" any of the sorted items that have been generated thus
    far.
    '''
    def __init__(self, relation_class, items, assumptions=USE_DEFAULTS,
                 skip_exact_reps=False, skip_equiv_reps=False,
                 presorted_pair=False):
        '''
        Create a TransitivitySorter object to sort the given
        'items' (and any added on the fly later) according to
        the relation_class (a TransitivityRelation) under the
        given assumptions.  If skip_exact_reps is True,
        only yield the first of an 'item' that is repeated
        exactly (equal Expressions).  If skip_equiv_reps is True,
        only yield the first of an 'item' that is repeated via
        a known equivalence.  If presorted_pair is True, use the
        sorter solely to confirm and prove that two given items
        were provided in sorted order.
        '''
        #print("sorting items", items)
    
        self.assumptions = defaults.checkedAssumptions(assumptions)
        self.assumptions_set = set(self.assumptions)
        self.relation_class = relation_class
        self.strong_relation_class = \
            relation_class._checkedStrongRelationClass()
        self.is_weak_relation = (relation_class != self.strong_relation_class)
        self.skip_exact_repetitions = skip_exact_reps
        self.skip_equiv_repetitions = skip_equiv_reps
        
        if presorted_pair:
            if len(items) != 2:
                raise ValueError("Only provide 2 items, not %d"%len(items)
                                   +", if presorted_pair is true.")

        self.remaining_items = set(items)
        
        # Use the original index of the item to maintain the original
        # order among equivalent items (or using the 'first' when
        # skip_equiv_repetitions is True).
        self.item_orig_idx = dict()
        for k, item in enumerate(items):
            # Note: use the index of the first occurrence of an item;
            self.item_orig_idx.setdefault(item, k) # do not overwrite.

        # When there are known equivalences, this will map each item
        # of an equivalence set to the full equivalence set:
        self.eq_sets = {item:{item} for item in items}
        # Representative for each equvalence set:
        self.eq_set_rep = {item:item for item in items}
        
        self.left_partners = dict()
        self.right_partners = dict()
        
        self.left_most_candidates = set(self.remaining_items)
        self.repetitions = {item:0 for item in self.remaining_items}
        for item in items: self.repetitions[item] += 1
        
        left_going_items = right_going_items = self.remaining_items
        if presorted_pair:
            left_item, right_item = items
            left_going_items = [right_item]
            right_going_items = [left_item]
                
        # Map each item to a list of (end-point, chain) pairs
        # where the end-point is reachable from the item via the chain
        # going left:
        self.frontier_left_chains = {item:deque([(item,[])]) 
                                     for item in left_going_items}
        # or going right:
        self.frontier_right_chains = {item:deque([(item,[])]) 
                                      for item in right_going_items}
            
        # Map left end-points to chains from the end-point to items:
        self.left_endpoint_chains = {item:[[]] for item in left_going_items} 
        # Map right end-points to chains from items to the end-point:
        self.right_endpoint_chains = {item:[[]] for item in right_going_items} 
        # Map each item to end-points reachable from that item
        # via generated chains going left:
        self.left_reachables = {item:set([item]) 
                                for item in left_going_items} 
        # Map each item to end-points reachable from that item 
        # via generated chains going right:
        self.right_reachables = {item:set([item]) 
                                 for item in right_going_items}

        self.item_pair_chains = dict() # (left-item, right-item): chain

        self.prev_reported = None
        
        # Flag to track whether there is anything new to process.
        self.more_to_process = True
        
        self._generator = self._generate_next_items()
    
    def add(self, item):
        '''
        Add a new item to be sorted.  It must be "beyond" any of the
        items that have thus far been "generated" in sorted order.
        '''
        #print("add item", item)
        self.more_to_process = True # something new to process
        if item in self.remaining_items:
            # Not a new item.  Just a repetition.
            self.repetitions[item] += 1
            return
        
        # Prepare for the new item.
        self.remaining_items.add(item)
        self.item_orig_idx[item]  = len(self.item_orig_idx)
        self.eq_sets[item] = {item}
        self.eq_set_rep[item] = item
        self.left_most_candidates.add(item)
        self.repetitions[item] = 1
        
        # Don't add the item to the "frontiers".  We want that
        # to happen in _generate_relations where it will take
        # care of other things as well (making connections to
        # existing chains, in particular).
        #self.frontier_left_chains[item] = deque([(item,[])])
        #self.frontier_right_chains[item] = deque([(item,[])])
        
        self.left_endpoint_chains[item] = [[]]
        self.right_endpoint_chains[item] = [[]]
        self.left_reachables[item] = {item}
        self.right_reachables[item] = {item}
    
    def __iter__(self):
        '''
        Iterate through the items in sorted order by using only known 
        relations.
        '''
        return self._generator
    
    def _generate_next_items(self):
        '''
        Generator to implement the __next__ method.
        '''
        from proveit.logic import Equals
        from .transitivity import TransitivityException
    
        # Generate relations between items via a breadth-first, 
        # meet-in-the-middle explorations of known relations for the 
        # purpose of sorting and use this information to successively 
        # identify "leftmost" items.  
        item_pair_chains = self.item_pair_chains
        eq_sets = self.eq_sets
        eq_set_rep = self.eq_set_rep
        left_partners = self.left_partners
        right_partners = self.right_partners
        assumptions = self.assumptions
        remaining_items = self.remaining_items
                
        # Left-most candidates are a representative set of items 
        # (representative up to equivalences) that have no left 
        # partners.  This starts as everything.  Items are removed when 
        # new relations are generated revealing new left-right 
        # partnerships and items are added after a definitive left-most 
        # item is yielded and removed as a left partner of other items.
        left_most_candidates = self.left_most_candidates
        
        while self.more_to_process:
            for (left_item, right_item), chain in self._generate_relations():
                if left_item not in self.remaining_items:
                    # Does not give new information 
                    continue # if the left item was sorted already.
                if (left_item, right_item) in item_pair_chains:
                    # Just use the first chain of relations between a pair
                    # of items.  If the relation is an equality between the 
                    # items, that should come first.
                    continue 
                                    
                # Add new item partnership to item_pair_chains.
                #print("add new partnership:", left_item, right_item)
                item_pair_chains[(left_item, right_item)] = chain
        
                # If the left and right items are equal,
                # record the equivalence.
                if all(relation.operator==Equals._operator_ for relation in chain):
                    # Equal relation goes both ways:
                    #item_pair_chains[(right_item, left_item)] = chain
                    if eq_sets[left_item] != eq_sets[right_item]: 
                        #print("join eq sets", left_item, right_item, eq_sets[left_item], eq_sets[right_item])
                        # Joining two equivalent sets that were not 
                        # previously known to be equivalent.
                        eq_set = eq_sets[left_item] | eq_sets[right_item]
                        eq_set_lst = list(eq_set)
                        # Make all the equivalent items point to the same 
                        # equivalence set:
                        for item in eq_set: eq_sets[item] = eq_set
                        rep = eq_set_lst[0] # an arbitrary representative.
                        for item in eq_set: eq_set_rep[item] = rep
                        # If either of the equivalence sets being joined
                        # were eliminated from left_most_candidates,
                        # eliminate all of them.
                        left_most_candidates_in_eq_set = \
                            eq_set.intersection(left_most_candidates)
                        if len(left_most_candidates_in_eq_set)==2:
                            # Only keep one of the left-most candidates 
                            # (an arbitrarily chosen representative):
                            extraneous = eq_set_lst[1:]
                            left_most_candidates.difference_update(extraneous)
                        else:
                            # One (or both) of the two equivalence sets 
                            # being joined was eliminated from the 
                            # left_most_candidates, so remove all of them 
                            # in this new equivalence set.
                            assert len(left_most_candidates_in_eq_set)<=1
                            left_most_candidates.difference_update(eq_set)
                else:
                    # Use equivalence set representatives for pair:
                    left_item = eq_set_rep[left_item]
                    right_item = eq_set_rep[right_item]
                    # Add new item partnership to left_partners, and 
                    # right_partners:
                    left_partners.setdefault(right_item, set()).add(left_item)
                    right_partners.setdefault(left_item, set()).add(right_item)  
                    # See if we can eliminate a left-most candidate:
                    if right_item in left_most_candidates:
                        # Remove the right item from the left-most 
                        # candidates because there is something to the left 
                        # of it now.
                        left_most_candidates.remove(right_item)
                        # Assume all cycles are accounted for via 
                        # equivalences; otherwise we'll catch it at some 
                        # point and raise the exception below.
                        if len(left_most_candidates)==0:
                            msg = ("Transitivity cycle detected implying"
                                "equalities indirectly; must prove equalities"
                                "before sorting items: " + str(remaining_items))
                            raise TransitivityException(None, assumptions, msg)
                
                #print("left candidates", left_most_candidates)
                for next_item in self._report_ready_items():
                    yield next_item
                
                # Check if finished:
                if len(remaining_items)==0: break
            
            # Nothing else to process unless something new is added after we report
            # items below.
            self.more_to_process = False
            
            # Any stragglers?
            #print("straggler left candidates", left_most_candidates)
            for next_item in self._report_ready_items():
                yield next_item
        
        if len(remaining_items) > 0:
            msg = ("Insufficient known transitive relations to sort"
                   " the remaining items: " + str(self.remaining_items))
            raise TransitivityException(None, assumptions, msg)
    
    def _report_ready_items(self):
        '''
        Report 'next' items and perform appropriate updates as long
        as there is a single left-most-candidate.
        '''
        eq_sets = self.eq_sets
        left_partners = self.left_partners
        right_partners = self.right_partners
        remaining_items = self.remaining_items
        left_most_candidates = self.left_most_candidates
        
        while len(left_most_candidates)==1:
            # We have one uncontested left-most candidate assuming 
            # no cycles outside of equivalence sets (with such 
            # cycles, we'll catch them eventually and raise an
            # exception).
            left_most = left_most_candidates.pop()

            left_most_equiv = eq_sets[left_most]
            
            # Report "left_most" as the next item the appropriate
            # number of times (depending upon whether equivalences
            # and repetitions should be skipped).
            for next_item in left_most_equiv:
                # If we have already reported an item, we must prove the
                # direct relationship between the next item and the 
                # previous one.
                if self.prev_reported is not None:
                    self._prove_direct_relationship_if_known(self.prev_reported, 
                                                            next_item)
                yield next_item
                self.prev_reported = next_item
                if not self.skip_exact_repetitions:
                    # Yield exact repetitions (if there are any).
                    for _ in range(self.repetitions[next_item]-1):
                        yield next_item
                if self.skip_equiv_repetitions:
                    # Just report one representative of
                    # an equivalence set.
                    break 
                        
            # Note that eq_sets[left_most] should not be extended 
            # later because all of the items must determine that 
            # they are either to the right of this "left-most" or 
            # equal to it before we got here.
            elim_items = left_most_equiv # to eliminate.
            remaining_items.difference_update(elim_items) 
            
            # Remove links to the left-most item so we can focus on 
            # the next left-most item.
            right_of_elim = set().union(*[right_partners.get(el_it, set()) 
                                            for el_it in elim_items])
            #print("right_of_elim", right_of_elim)
            for right_partner in right_of_elim:
                # Is there anything remaining to the left of this right
                # partner?
                left_of_right_partner = set()
                for rp in eq_sets[right_partner]:
                    left_of_rp = left_partners.get(rp, set())
                    # Discard the 'elim_items' from the left partners of
                    # each right partner.
                    left_of_rp.difference_update(elim_items)
                    left_of_right_partner.update(left_of_rp)
                #print("right_partner", right_partner, left_of_right_partner)
                if len(left_of_right_partner)==0:
                    # A new left-most candidate emerges when its 
                    # last left partnership is removed.
                    left_most_candidates.add(right_partner)
            
            # Note that we may end up with multiple left-most 
            # candidates in which case more links are needed.        
    
    def _generate_relations(self):
        '''
        Use a breadth-first approach to generate relations
        emanating from left-most candidates so they can be
        eliminated as candidates one by one.  Adapts to changes
        in the left-most candidate set and additions of items
        to be sorted.
        '''
        if len(self.remaining_items)==1:
            return # no relationships when there is just one item
        
        relation_class = self.relation_class
        assumptions_set = self.assumptions_set
        left_most_candidates = self.left_most_candidates
        eq_sets = self.eq_sets
        eq_set_rep = self.eq_set_rep
        
        # For each item (and direction), track the known relation 
        # iterator for the frontier end-point currently being extended.
        # Used within the 'next_relation' internal function (below). 
        active_known_relations_by_item = dict()
        # The chain corresponding to the active known relation iterator.
        active_chain_by_item = dict()
        
        def next_chain(item, frontier_chains, reachables, known_relations):
            '''
            Return the next breadth-first chain, and corresponding
            endpoint, extending from the given item or 
            None if all its extensions have been exhausted.
            '''
            # Identify the directon (left-going or right-going)
            # by the id of the corresponding frontier_chains.
            dir_id = id(frontier_chains)
            chains = frontier_chains[item]
            try:
                item_reachables = reachables[item]
            except KeyError as e:
                # No relations
                return None, None
            # Choose a relation to extend the frontier.
            while True:
                try:
                    relation, new_endpoint = \
                        next(active_known_relations_by_item[(item, dir_id)])
                    if new_endpoint in item_reachables:
                        # Nothing new.  Try again.
                        continue
                    if new_endpoint in chains:
                        # Not really a new end-point; same as a known 
                        # end-point (this can happen via the reflexivity
                        # of equality).
                        continue 
                    chain = active_chain_by_item[(item, dir_id)] 
                    if frontier_chains is self.frontier_left_chains:
                        # Extend chain to the left:
                        return [relation] + chain, new_endpoint
                    else:
                        # Extend chain to the right:
                        return chain + [relation], new_endpoint
                except (KeyError, StopIteration):
                    # Pop another endpoint off the item's 
                    # "frontier".
                    if len(chains)==0:
                        # We have exhausted this frontier.
                        # We are done extending this item.
                        # Signal the end for this item:
                        return None, None
                    # FIFO to be breadth-first.
                    endpoint, active_chain_by_item[(item, dir_id)] = \
                        chains.popleft()
                    active_known_relations_by_item[(item, dir_id)] = \
                        known_relations(endpoint, assumptions_set)
        
        # Keep working until no new extensions can be generated.
        new_extensions = True
        while new_extensions:
            new_extensions = False
            
            # Alternate extending item frontiers to the left then to
            # the right in a breadth-first manner.
            lr_frontier_chains = (self.frontier_left_chains, 
                                  self.frontier_right_chains)
            lr_reachables = (self.left_reachables, self.right_reachables)
            lr_relations = (relation_class.knownRelationsFromRight, 
                            relation_class.knownRelationsFromLeft)
            lr_same_endpoint_chains = (self.left_endpoint_chains, 
                                       self.right_endpoint_chains)
            lr_opposite_endpoint_chains = (self.right_endpoint_chains,
                                           self.left_endpoint_chains)
            for (frontier_chains, reachables, known_relations,
                 same_endpoint_chains, opposite_endpoint_chains) in \
                    zip(lr_frontier_chains, lr_reachables, lr_relations, 
                        lr_same_endpoint_chains, lr_opposite_endpoint_chains):
                
                # Extend chains originating from each of the left-most
                # candidates (or equivalent items) in a effort to widdle 
                # down these candidates.  The left-most candidates will 
                # be updated as relations are yielded, so it is 
                # important that we iterate over a copy and check if it
                # is still in the list of candidates.  When a left-most 
                # candidate is added it will be treated in the next 
                # round.
                items_of_interest = set().union(*[eq_sets[item] for item in
                                                  left_most_candidates])
                for item in items_of_interest:
                    if eq_set_rep[item] not in left_most_candidates:
                        # This item (or its equivalent representative)
                        # is no longer a left-most candidate.  Skip it.
                        continue
                    
                    if item in frontier_chains:
                        # Extend the frontier of 'item'.
                        # Choose a relation to extend the frontier.
                        
                        new_chain, new_endpoint = \
                            next_chain(item, frontier_chains, reachables,
                                       known_relations)
                        if new_chain is None:
                            # No more chains on this item's frontier.
                            continue 
                    elif item in reachables:
                        # A newly added item starting fresh but
                        # may already connect with existing chains.
                        frontier_chains[item] = deque([(item,[])])
                        new_endpoint = item
                        new_chain = []
                    else:
                        # If it isn't in either frontier_chain or
                        # reachables, it is not a new item.  Rather,
                        # it is a presorted_pair situation
                        # where each item is uni-directional and this
                        # is simply the 'wrong' direction).
                        continue

                    # There is something new this round at least.
                    # (A new chain or a new item to start extending
                    # from).
                    new_extensions = True
                                                
                    # See if we meet an opposing chain to connect this 
                    # item with another one (meeting in the "middle").
                    has_yielded_a_chain = False
                    if new_endpoint in opposite_endpoint_chains:
                        meeting_chains = opposite_endpoint_chains[new_endpoint]
                        # Include all but the obsolete "meeting_chains":
                        updated_meeting_chains = []
                        for meeting_chain in meeting_chains:
                            if frontier_chains is self.frontier_left_chains:
                                # Left-going chain (new_chain) meeting 
                                # with right-going chain (meeting_chain)
                                if len(meeting_chain)>0:
                                    other_item = meeting_chain[0].operands[0] 
                                else:
                                    other_item = new_endpoint
                                left_item, right_item = other_item, item
                                #print("left-meeting-right", meeting_chain, new_endpoint, new_chain)
                                chain = meeting_chain + new_chain
                            else:
                                assert (frontier_chains is 
                                        self.frontier_right_chains), \
                                        "Should be either left or right"
                                # Right-going chain (new_chain) meeting
                                # with left-going chain (meeting_chain)
                                if len(meeting_chain)>0:
                                    other_item = meeting_chain[-1].operands[-1] 
                                else:
                                    other_item = new_endpoint
                                left_item, right_item = item, other_item
                                #print("right-meeting-left", new_chain, new_endpoint, meeting_chain)
                                chain = new_chain + meeting_chain
                            if other_item in self.remaining_items: 
                                # Remember chains that are still
                                # relevent; forget what is obsolete.
                                updated_meeting_chains.append(meeting_chain)
                                if left_item != right_item:
                                    # A new relation to yield, as long
                                    # as the chain has the proper 
                                    # "strength" (if the relation is
                                    # strong, it must have at list one
                                    # strong link).
                                    if self.is_weak_relation \
                                            or self._is_strong_chain(chain):
                                        has_yielded_a_chain = True
                                        yield ((left_item, right_item), chain)
                        # Remove chains that are obsolete -- going to
                        # items that are no longer "remaining":
                        opposite_endpoint_chains[new_endpoint] = \
                            updated_meeting_chains
                    
                    # Is it redundant to continue the chain starting
                    # from 'item' going to 'new_endpoint'?  It may
                    # be redundant if 'new_endpoint' is one of the
                    # remaining items also being tracked such that
                    # we'll get what we need from 'new_endpoint'
                    # directly, but only if there was a proper
                    # chain going to 'new_endpoint' (not weak when
                    # we need a strong relation) and not if 'item' is
                    # the representative of an equivalence set that
                    # includes 'new_endpoint'.
                    # Start guilty until proven innocent:
                    redundant_endpoint = True 
                    if not has_yielded_a_chain: 
                        # Not a proper chain from item to new_endpoint.
                        redundant_endpoint = False # Not redudant.
                    elif new_endpoint not in self.remaining_items:
                        # The new_endpoint is not tracked on its own.
                        redundant_endpoint = False # Not redundant.
                    elif eq_set_rep.get(new_endpoint, None)==item:
                        # The item is the representative of the
                        # equivalent set that includes the new endpoint.
                        redundant_endpoint = False # Not redundant.
                                        
                    # Unless it is redundant, we need to continue
                    # tracking this frontier from the 'item'.              
                    if not redundant_endpoint:
                        lst=same_endpoint_chains.setdefault(new_endpoint, [])
                        lst.append(new_chain)
                        # Extend the chain to a new endpoint:
                        frontier_chains[item].append((new_endpoint, new_chain))
                        # A new reachable end-point:
                        reachables[item].add(new_endpoint)
    
    def _is_strong_chain(self, chain):
        '''
        Return true iff there exists a strong relation within the
        given chain.
        '''
        for relation in chain:
            if relation.expr.__class__ == self.strong_relation_class:
                return True
        return False
        
    def _prove_direct_relationship_if_known(self, item1, item2):
        '''
        Apply necessary transitivities to prove a direct relationship
        between item1 and item2 there is a known chain.  There may not
        be a known chain if the order is relying on the assertion that
        added items cannot come before previous items.
        '''
        from proveit.logic import Equals
        item_pair_chains = self.item_pair_chains
        relation_class = self.relation_class
        assumptions = self.assumptions
        eq_sets = self.eq_sets
        if (item1, item2) not in item_pair_chains:
            # We may not have the chain for these specific items, but
            # we should have it for something equivalent to each of the 
            # items (unless item2 was added after item1 and only 
            # presumed to come later w.r.t. the transitive relation).
            for eq_item1, eq_item2 in itertools.product(eq_sets[item1],
                                                         eq_sets[item2]):
                
                if (eq_item1, eq_item2) not in item_pair_chains:
                    # Maybe the relationship is known even though it 
                    # isn't in item_pair_chains.  This can be a useful 
                    # check in cases of merge sorting where some of the 
                    # relationships are presumed.
                    for rel_class in self.relation_class._RelationClasses():
                        try:
                            rel = rel_class(eq_item1, eq_item2)
                            rel.prove(assumptions, automation=False)
                            item_pair_chains[(eq_item1, eq_item2)] = [rel]
                            break # We got all we need
                        except:
                            pass
                                                                      
                if (eq_item1, eq_item2) in item_pair_chains:
                    # If item1, eq_item1 are not identical expressions,
                    # prove that they are logically equal.
                    if item1 != eq_item1:
                        prepend = [Equals(item1, eq_item1).prove(assumptions)]
                    else: 
                        prepend = [] 
                    # If item2, eq_item2 are not identical expressions, 
                    # prove that they are logically equal.
                    if item2 != eq_item2:
                        append = [Equals(eq_item2, item2).prove(assumptions)]
                    else:
                        append = []
                    # Make the (item1, item2) chain by 
                    # prepending/appending necessary equalities to the
                    # (eq_item1, eq_item2) chain
                    chain = (prepend 
                             + item_pair_chains[(eq_item1, eq_item2)]
                             + append)
                    item_pair_chains[(item1, item2)] = chain
                    break # We only need one.
        
        #print("after chains", item_pair_chains)
        if (item1, item2) in item_pair_chains:
            chain = item_pair_chains[(item1, item2)]
            #print("prove direct relationship via", chain)
            self.relation_class.applyTransitivities(chain, assumptions)

