from proveit import ExprTuple, InnerExpr, Literal, Operation, USE_DEFAULTS
# from proveit.abstract_algebra.generic_methods import apply_permutation_thm
from proveit.abstract_algebra.generic_methods import (
        apply_commutation_thm, generic_permutation)

class Set(Operation):
    '''
    Defines an enumerated set (i.e. a set with explicitly-listed
    elements). For example, one could use Set(one, two, three) to
    produce the enumerated set {1, 2, 3} or Set(a, b, a) to produce
    the enumerated set {a, b, a}. Although repeated elements can be
    specified and will appear in output expressions, the Set is
    interpreted as a set and not a multiset --- thus, e.g., we have
    {a, b, a} = {a, b} and the cardinality of an enumerated Set such
    as {a, b, a} should be the cardinality of the underlying support
    {a, b}.
    '''
    
    # operator of the Set operation
    _operator_ = Literal(stringFormat='Set', context=__file__) 
    
    def __init__(self, *elems):
        Operation.__init__(self, Set._operator_, elems)
        self.elements = self.operands
    
    def membershipObject(self, element):
        from .enum_membership import EnumMembership
        return EnumMembership(element, self)

    def nonmembershipObject(self, element):
        from .enum_membership import EnumNonmembership
        return EnumNonmembership(element, self)

    def string(self, **kwargs):
        return '{' + self.elements.string(fence=False) + '}'
    
    def latex(self, **kwargs):
        return r'\left\{' + self.elements.latex(fence=False) + r'\right\}'

    def permutation_move(self, initIdx=None, finalIdx=None,
                         assumptions=USE_DEFAULTS):
        '''
        and use a permutationSwap for the extra one (use swap for the verb)
        Deduce that this Set expression is equal to a Set
        in which the element at index initIdx has been moved to
        finalIdx. For example, {a, b, c, d} = {a, c, b, d} via
        initIdx = 1 (i.e. 'b') and finalIdx = -2. In traditional
        cycle notation, this corresponds to an index-based cycle
        (initIdx, initIdx+1, … finalIdx) where
        0 ≤ initIdx ≤ finalIdx ≤ n - 1 for a set of size n.
        '''
        from ._theorems_ import (binaryPermutation, leftwardPermutation,
                                 rightwardPermutation)
        return apply_commutation_thm(self, initIdx, finalIdx, binaryPermutation,
                                     leftwardPermutation, rightwardPermutation,
                                     assumptions)

    # ============================================================== #
    # Might be useful to have a special swap version of permutation
    # def permutation_swap
    # register with swapped as the adjective, swap as the verb
    # ============================================================== #

    def permutation(self, new_order=None, cycles=None,
                    assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression is set-equivalent to a Set
        in which the elements at indices 0, 1, …, n-1 have been
        reordered as specified EITHER by the new_order list OR by the
        cycles list parameter. For example,
        {a, b, c, d}.permutationGeneral(new_order=[0, 2, 3, 1]) and
        {a, b, c, d}.permutationGeneral(cycles=[(1, 2, 3)]) would both
        return |- {a, b, c, d} = {a, c, d, b}.
        '''
        return generic_permutation(self, new_order, cycles, assumptions)


    def deduceEnumSubsetEq(self, subset_indices=None, subset=None,
                         assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression has as an improper subset the
        set specified by either the indices in subset_indices list or
        the Set() specified by subset (but not both).
        For example, both
        {a, b, c, d}.deduceEnumSubsetEq(subset_indices=[1, 3]) and
        {a, b, c, d}.deduceEnumSubsetEq(subset=Set(b, d))
        return |– {b, d} subsetEq {a, b, c, d}.
        This process is complicated by the fact that the Set class
        allows for multiplicity of elements without actually
        representing a multi-set (thus, for example, {a, a} = {a}).
        '''

        from proveit.logic import Set

        # Before bothering with much processing, quickly check that:
        # (1) user has specified subset_indices OR subset but not both;
        # (2) if only subset specification, it has the correct form;
        # (3) if only subset_indices, they are plausible.
        if subset_indices is None and subset is None:
            raise ValueError("Need to specify the desired subset by "
                             "specifying the list of indices (subset_indices) "
                             "OR an actual subset (in the form of an "
                             "enumerated set using Set()).")
        if subset_indices is not None and subset is not None:
            raise ValueError("Need to specify the desired subset by "
                             "specifying the list of indices (subset_indices) "
                             "OR an actual subset, but NOT both.")
        if subset is not None and not isinstance(subset, Set):
            raise ValueError("Specified subset {} does not appear to be a "
                             "valid Set object.".format(subset))
        self_list = list(self.operands)
        valid_indices_list = list(range(0, len(self.operands)))

        if subset_indices is not None:
            # We must have had subset=None, so check validity of the
            # indices and use them to create a subset Set
            self._check_subset_indices_weak(valid_indices_list, subset_indices)
            subset_list_from_indices = [self_list[i] for i in subset_indices]
            subset_from_indices = Set(*subset_list_from_indices)
            subset = subset_from_indices

        # We should now have a subset Set, either explicitly provided
        # as an argument or derived from the subset_indices.
        # A subset generated from the subet_indices will automatically
        # be a plausible subset (b/c it derived from the superset self
        # elements). If the subset was originally supplied as
        # an argument, however, we still need to check if it is a
        # plausible subset of self: it should only have elements found
        # in self or elements somehow proven to be equal to elements
        # in self.
        subset_was_substituted = False
        if subset_indices == None: # subset provided by user

            # then our subset and subset_reduced might have issues
            subset_list = list(subset.operands) 
            error_elem_candidates = set()
            error_elem_equivalences_dict = dict()
            for elem in set(subset_list):
                if elem not in set(self_list):
                    error_elem_candidates.add(elem)

            if len(error_elem_candidates)>0:
                # We have candidates in the supposed subset that do not
                # literally appear in the supposed superset self, but
                # the candidates might be known to be 'equal' to
                # appropriate values, so we check just a little more
                # assiduously before returning an error message
                error_elems = error_elem_candidates.copy()
                from proveit.logic import Equals
                for elem in error_elem_candidates:
                    for super_elem in set(self_list):
                        print("Checking if {0} = {1}".format(elem, super_elem)) # for testing; delete later
                        if Equals(elem, super_elem).proven(
                                assumptions=assumptions):
                            print("Equals(elem, super_elem).proven(): {}".
                                format(Equals.knownEqualities[elem]))
                            error_elems.discard(elem)
                            # add to dict for later processing
                            error_elem_equivalences_dict[elem]=super_elem
                            # only need elem to be equal to one super_elem
                            break 
                if len(error_elems) > 0:
                    raise ValueError(
                            "Specified subset {0} does not appear to be a subset "
                            "of the original set {1}. The following elements "
                            "appear in the requested subset Set but not in the "
                            "original Set: {2}.".
                            format(subset, self, error_elems))
                print("error_elem_equivalences: {}".format(
                        error_elem_equivalences_dict))
                # use any equivalences found above and stored in dict
                # to deduce subset equal to the set obtained when the
                # substitutions are made
                temp_subset = subset
                from proveit import TransRelUpdater
                eq = TransRelUpdater(temp_subset, assumptions)
                print("eq.relation = {}".format(eq.relation))
                for key in error_elem_equivalences_dict:
                    print("key = {}".format(key));
                    print("dict[key] = {}".format(
                        error_elem_equivalences_dict[key]))
                    temp_subset = eq.update(temp_subset.elem_substitution(
                            elem=key, sub_elem=error_elem_equivalences_dict[key],
                            assumptions=assumptions))
                print("eq.relation = {}".format(eq.relation))
                print("temp_subset = {}".format(temp_subset))
                subset = temp_subset
                subset_to_substituted_subset_kt = eq.relation
                subset_was_substituted = True

        # Derive the reduced form of the self Set. We could have done
        # this earlier, but delayed until after param checking.
        # The eventual subset relationship will be based on the
        # reduced forms of the specified Sets.
        self_to_support_kt = self.reduction(assumptions=assumptions)
        self_reduced = self_to_support_kt.rhs
        self_reduced_list = list(self_reduced.operands)

        # Derive the reduced form of the subset Set.
        # The eventual subset relationship will be based
        # on the reduced forms of the specified Sets.
        subset_to_support_kt = subset.reduction(assumptions=assumptions)
        subset_reduced = subset_to_support_kt.rhs
        subset_reduced_list = list(subset_reduced.operands)
        
        # For convenience, convert the subset_reduced_list to indices
        # of the self_reduced_list. Because of earlier checks, the
        # subset_reduced_list should not contain any items not also
        # contained in self_reduced_list.
        subset_reduced_indices_list = (
            [self_reduced_list.index(elem) for elem in subset_reduced_list])

        full_indices_list = list(range(0, len(self_reduced_list)))

        # construct the complement of the subset indices
        # avoiding using sets to preserve order just in case
        remaining_indices = list(full_indices_list) # clone
        for elem in subset_reduced_indices_list:
            remaining_indices.remove(elem)

        # establish the desired order for eventual thm application
        new_order = subset_reduced_indices_list + remaining_indices
        # find superset permutation needed for thm application
        supersetPermRelation = generic_permutation(
                self_reduced, new_order, assumptions=assumptions)
        # construct the desired list of subset elems
        desired_subset_list = subset_reduced_list
        # construct the desired complement list of elems
        desired_complement_list = []
        for elem in remaining_indices:
            desired_complement_list.append(self_reduced_list[elem])

        # Organize info for theorem specialization
        # then specialize.
        from ._theorems_ import subsetEqOfSuperset
        # from proveit._common_ import m, n, aa, bb
        from proveit.number import num
        m, n, a, b = subsetEqOfSuperset.allInstanceVars()
        a_sub, b_sub = (desired_subset_list, desired_complement_list)
        m_sub, n_sub = num(len(a_sub)), num(len(b_sub))
        subset_of_permuted_superset = subsetEqOfSuperset.specialize(
                {m:m_sub, n:n_sub, a:a_sub, b:b_sub},
                assumptions=assumptions)

        # We now have |- reduced_subset \subseteq reduced_superset.
        # We back-sub to get the original subset as a subsetEq of the
        # original superset (self):
        # (1) Replace permuted reduced superset with unpermuted reduced
        #     superset:
        reduced_subset_of_reduced_superset = (
                supersetPermRelation.subLeftSideInto(
                        subset_of_permuted_superset.innerExpr().rhs))
        # (2) Replace reduced superset with original superset:
        reduced_subset_of_orig_superset = (
                self_to_support_kt.subLeftSideInto(
                        reduced_subset_of_reduced_superset))
        
        # (3) Replace the reduced (and possibly substituted) subset
        #     with the non-reduced (and possibly substituted) subset:
        substituted_subset_of_orig_superset = (
                subset_to_support_kt.subLeftSideInto(
                        reduced_subset_of_orig_superset))

        # (4) If we performed substitutions into the subset, replace
        #     the substituted subset with the original subset
        if subset_was_substituted:
            orig_subset_of_orig_superset = (
                    subset_to_substituted_subset_kt.subLeftSideInto(
                        substituted_subset_of_orig_superset))
            return orig_subset_of_orig_superset
        else:
            # no substitutions into subset performed earlier, so no
            # back-substitution needed:
            return substituted_subset_of_orig_superset


    def deduceEnumProperSubset(self, subset_indices=None, subset=None,
                               assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression has as a proper subset the
        set specified by either (a) the indices in the subset_indices 
        list OR (b) the Set specified by subset (but not both).
        For example, both
        {a, b, c, d}.deduceEnumSubset(subset_indices=[1, 3]) and
        {a, b, c, d}.deduceEnumSubset(subset=Set(b, d))
        return |– {b, d} subset {a, b, c, d} (assuming the appropriate
        knowledge about either a or c (or both) not being elements of
        the subset {b, d}).
        This process is complicated by the fact that the Set class
        allows for multiplicity of elements without actually
        representing a multi-set (thus, for example, {a, a} = {a}).
        Subset deductions are based on the support sets for the self
        and subsets supplied.
        '''

        from proveit.logic import Set

        # Before bothering with much processing, quickly check that:
        # (1) user has specified subset_indices OR subset but not both;
        # (2) if only subset specification, it has the correct form;
        # (3) if only subset_indices, they are plausible.
        if subset_indices is None and subset is None:
            raise ValueError("Need to specify the desired subset by "
                             "specifying the list of indices (subset_indices) "
                             "OR an actual subset (in the form of an "
                             "enumerated set using Set()).")
        if subset_indices is not None and subset is not None:
            raise ValueError("Need to specify the desired subset by "
                             "specifying the list of indices (subset_indices) "
                             "OR an actual subset, but NOT both.")
        if subset is not None and not isinstance(subset, Set):
            raise ValueError("Specified subset {} does not appear to be a "
                             "valid Set object.".format(subset))
        self_list = list(self.operands)
        valid_indices_list = list(range(0, len(self.operands)))

        if subset_indices is not None:
            # We must have had subset=None, so check validity of the
            # indices and use them to create a subset Set
            self._check_subset_indices_weak(
                valid_indices_list, subset_indices, proper_subset=True)
            subset_list_from_indices = [self_list[i] for i in subset_indices]
            subset_from_indices = Set(*subset_list_from_indices)
            subset = subset_from_indices

        # If we make it this far we should have an explicit subset
        # Set, either explicitly provided or derived from the
        # subset_indices. We still need to check if the subset is a
        # provably proper subset (it should only have elements found
        # in the original self Set and the self Set should contain at
        # least one element not included in the supposed subset).
        # We'll also store away any such superset elems we find that
        # are candidates for not also being in the subset, and the first
        # superset elem we find that is actually provably not in
        # the subset.
        non_subset_elem_candidates = []
        non_subset_elem_proven = None
        non_subset_elem_index = None
        non_subset_elem_kt = None
        subset_list = list(subset.operands)
        # check that all subset elems appear in superset
        error_elems = []
        for elem in subset_list:
            if elem not in self_list:
                error_elems.append(elem)
        if len(error_elems)>0:
            raise ValueError(
                    "Specified subset {0} does not appear to be a subset "
                    "of the original set {1}. The following elements "
                    "appear in the supposed subset Set but not in the "
                    "original Set: {2}.".
                    format(subset, self, error_elems))
        # check that at least one superset elem does not appear in
        # subset. This is not a proof, just a superficial check that
        # there at least APPEAR to be elements in self that do not
        # appear in the subset (but we can be fooled by variables).
        # Those candidates will then be checked more carefully later
        # using the reduced forms of the sets.
        for elem in self_list:
            if (elem not in subset_list and
                elem not in non_subset_elem_candidates):
                non_subset_elem_candidates.append(elem)
        # if no candidate elements, raise an error
        if len(non_subset_elem_candidates) == 0:
            raise ValueError(
                    "Specified subset {0} does not appear to be a proper "
                    "subset of the original set {1}. All of the superset "
                    "elements appear in the specified subset.".
                    format(subset, self))
        # but if we have candidates, see if at least one can be proven
        # to not be in the subset
        else:
            # Try to prove that at least one of the non_subset_elems
            # really is not in the subset; this will then allow us
            # to sub properly in the properSubsetOfSuperset theorem.
            from proveit.logic import NotInSet
            for elem in non_subset_elem_candidates:
                try:
                    print("Checking if elem {0} is in subset {1}.".
                          format(elem, subset))
                    non_subset_elem_kt = NotInSet(elem, subset).prove(
                        assumptions=assumptions)
                    non_subset_elem_proven = elem
                    break
                except:
                    pass
            print("non_subset_elem_proven: {}".format(non_subset_elem_proven))
            print("non_subset_elem_kt: {}".format(non_subset_elem_kt))
            if non_subset_elem_proven is None:
                raise ValueError(
                    "Failed to prove that the supposed Self superset {0} "
                    "has any elements not already contained in the "
                    "supposed proper subset {1}.".
                    format(self, subset))


        # Derive the reduced form of the self superset Set. We could
        # have done this earlier, but delayed until after param
        # checking. The eventual (proper) subset relationship will be
        # based on the reduced forms of the specified Sets.
        self_to_support_kt = self.reduction(assumptions=assumptions)
        self_reduced = self_to_support_kt.rhs
        self_reduced_list = list(self_reduced.operands)
        # while we're here, get the index of the non_subset_elem_proven
        non_subset_elem_index = self_reduced_list.index(non_subset_elem_proven)
        print("    self_reduced_list: {}".format(self_reduced_list))
        print("    non_subset_elem_proven: {}".format(non_subset_elem_proven))
        print("    non_subset_elem_index: {}".format(non_subset_elem_index))

        # Derive the reduced form of the subset Set.
        # The eventual subset relationship will be based on the
        # reduced forms of the specified Sets.
        subset_to_support_kt = subset.reduction(assumptions=assumptions)
        subset_reduced = subset_to_support_kt.rhs
        subset_reduced_list = list(subset_reduced.operands)
        # While we're here, establish the non_subset_elem_proven as not
        # in the reduced subset as well, just in case (this helps with
        # some relatively rare cases where an elem not in a larger set
        # does not easily translate to elem not in a smaller, reduced
        # set)
        subset_to_support_kt.subRightSideInto(
                non_subset_elem_kt, assumptions=assumptions)
        
        # For convenience, convert the subset_reduced_list to indices
        # of the self_reduced_list. Because of earlier checks, the
        # subset_reduced_list should contain only items in
        # self_reduced_list but not all the items in self_reduced_list.
        subset_reduced_indices_list = (
            [self_reduced_list.index(elem) for elem in subset_reduced_list])

        full_indices_list = list(range(0, len(self_reduced_list)))

        # construct the complement of the subset_reduced_indices_list,
        # to use in the eventual construction of the necessary
        # permutation of the self superset Set.
        remaining_indices = list(full_indices_list) # clone
        for elem in subset_reduced_indices_list:
            remaining_indices.remove(elem)
        # then also remove the index for the non_subset_elem_proven
        remaining_indices.remove(non_subset_elem_index)

        # establish the desired order for eventual thm application
        new_order = (subset_reduced_indices_list + [non_subset_elem_index] +
                     remaining_indices)
        print("    new_order: {}".format(new_order))
        # find superset permutation needed for thm application
        supersetPermRelation = generic_permutation(
                self_reduced, new_order, assumptions=assumptions)
        # construct the desired list of subset elems
        desired_subset_list = subset_reduced_list
        # construct the desired complement list of elems
        desired_complement_list = [non_subset_elem_proven]
        for elem in remaining_indices:
            desired_complement_list.append(self_reduced_list[elem])

        # Organize info for theorem specialization
        # then specialize.
        from ._theorems_ import properSubsetOfSuperset
        from proveit.number import num
        m, n, a, b, c = properSubsetOfSuperset.allInstanceVars()
        a_sub = desired_subset_list
        b_sub = desired_complement_list[0]
        c_sub = desired_complement_list[1:]
        m_sub, n_sub = num(len(a_sub)), num(len(c_sub))
        subset_of_permuted_superset = properSubsetOfSuperset.specialize(
                {m:m_sub, n:n_sub, a:a_sub, b:b_sub, c:c_sub},
                assumptions=assumptions)

        # We now have |- reduced_subset \propersubset reduced_superset.
        # We back-sub to get the original subset as a proper subset of
        # the original superset (self):
        # (1) Replace permuted reduced superset with unpermuted reduced
        #     superset:
        reduced_subset_of_reduced_superset = (
                supersetPermRelation.subLeftSideInto(
                        subset_of_permuted_superset, assumptions=assumptions))
        # (2) Replace reduced superset with original superset:
        reduced_subset_of_orig_superset = (
                self_to_support_kt.subLeftSideInto(
                        reduced_subset_of_reduced_superset,
                        assumptions=assumptions))
        # (3) Replace the reduced subset with original subset:
        orig_subset_of_orig_superset = (
                subset_to_support_kt.subLeftSideInto(
                        reduced_subset_of_orig_superset,
                        assumptions=assumptions))

        return orig_subset_of_orig_superset


    def reduction(self, assumptions=USE_DEFAULTS):
        '''
        Deduce that this enum Set expression is equal to the Set's
        support -- i.e. equal to a Set with all multiplicities reduced
        to 1. For example, the Set(a, a, b, b, c, d)={a, a, b, b, c, d}
        is equal to its support {a, b, c, d}. The deduction is
        achieved by successively applying the element-by-element
        reduction_elem() method until no further reduction is possible.
        Created 02/08/2020 by wdc.
        Last modified 02/08/2020 by wdc:
            Creation; established input param checking
        '''
        from proveit import TransRelUpdater
        eq = TransRelUpdater(self, assumptions)
        current_operands = list(self.operands)
        # the following does not preserve the order, but we really
        # just want the size of the support set
        desired_operands = set(self.operands)
        desired_num_operands = len(set(self.operands))
        expr = self
        while len(current_operands) > desired_num_operands:
            expr = eq.update(expr.reduction_elem(assumptions=assumptions))
            current_operands = expr.operands

        return eq.relation


    def reduction_elem(self, elem=None, idx=None, assumptions=USE_DEFAULTS):
        '''
        Deduce that this enum Set expression is equal to a Set
        in which the multiply-occurring element specified either by
        elem or by the position idx has been removed from the set.
        If elem specified, method attempts to delete the 2nd occurrence
        of elem from the set. If neither elem nor idx specified,
        method attempts to delete the first repeated element of the Set.
        If both elem and idx are specified, the elem param is ignored.
        Examples: Let S = Set(a, b, a, b, a, c). Then
        S.reduction_elem() gives |-S = {a, b, b, a, c};
        S.reduction_elem(elem=b) gives |- S = {a, b, a, a, c};
        S.reduction_elem(idx=4) gives |- S = {a, b, a, b, c}.
        Consider changing name to elem_reduction, then use elem_reduced
        as adj and elem_reduce as verb.
        '''
        n = len(self.operands)

        # if user has specified position index idx,
        # check for validity and use  idx if possible
        if idx is not None and (idx < -n or idx >= n):
            raise IndexError("Index specification idx is out of bounds: {0}. "
                             "Need {1} ≤ idx ≤ {2}.".
                             format(idx,-n, n-1))
        if idx is not None:
            # we already checked for valid idx, so
            # transform any wrap-around indexing for simplicity
            if idx < 0: idx = n+idx
            # check if idx corresponds to an elem that repeats
            elem = self.operands[idx]
            if list(self.operands).count(elem) < 2:
                raise ValueError("The element '{0}' specified at index "
                                 "idx={1} occurs just once in the enum Set "
                                 "and thus cannot be eliminated.".
                                 format(elem, idx))

        # if user has specified elem instead of position index
        # check validity and use if possible by converting to
        # a positional index value
        if idx is None and elem is not None:
            # find index of 2nd occurrence of elem, if it exists
            # first gen enumerated list of those repeated elems
            idx_list_of_elem = (
                [i for i,j in enumerate(self.operands) if j == elem])
            temp_len = len(idx_list_of_elem)
            if temp_len < 2:
                if temp_len == 0:
                    temp_err_string = 'zero times'
                else:
                    temp_err_string = 'just 1 time'
                raise ValueError("Specified element '{0}' appears {1} "
                                 "in the enum Set and thus cannot be "
                                 "eliminated.".
                                 format(elem, temp_err_string))
            else:
                idx = idx_list_of_elem[1]

        # if user has specified NEITHER elem NOR positional index idx
        # find first repeated element (if it exists) and use
        # its positional index for idx
        if idx is None and elem is None:
            # check if there are ANY repeating elements:
            if len(self.operands) == len(set(self.operands)):
                raise ValueError("{0} appears to already be in reduced form.".
                                 format(self))
            else: # find first repeated elem
                already_seen = set()
                for i, elem in enumerate(self.operands):
                    if elem in already_seen:
                        idx = i
                        break
                    already_seen.add(elem)

        # now that idx is OK determine location of a matching elem
        # that will remain (so we can apply one of our reduction thms)
        idx_to_elim = idx  # index of elem to eliminate
        idx_to_keep = -1   # index of matching elem to keep
        elem_to_elim = self.operands[idx_to_elim]
        idxs_of_elems = (
            [i for i,j in enumerate(self.operands) if j == elem_to_elim])
        if idx_to_elim != idxs_of_elems[0]:
            # elem to keep is left of elem to eliminate
            idx_to_keep = idxs_of_elems[0]
        else:
            # elem to keep is right of elem to eliminate
            idx_to_keep = idxs_of_elems[1]


        # Now ready to apply the single-elem reduction theorem
        from ._theorems_ import reduction_right, reduction_left
        from proveit._common_ import l, m, n, x, aa, bb, cc
        from proveit.number import num
        l, m, n, aa, x, bb, cc = reduction_right.allInstanceVars()

        # NOTICE most of this is the same whether we are eliminating an
        # extra element to the right or to the left of an id'd element
        idx_left = min(idx_to_keep, idx_to_elim)
        idx_right = max(idx_to_keep, idx_to_elim)
        # so we break the set in into [ ]+[idx_left]+[ ]+[idx_right]+[ ]
        l_sub, m_sub, n_sub = (num(idx_left),
                               num(idx_right - idx_left - 1),
                               num(len(self.operands)-1-idx_right))
        aa_sub, x_sub, bb_sub, cc_sub = (
                list(self.operands)[0:idx_left],
                list(self.operands)[idx_left],
                list(self.operands)[idx_left + 1: idx_right],
                list(self.operands)[idx_right + 1:])
        if idx_to_keep < idx_to_elim:
            return reduction_right.specialize(
                {l:l_sub, m:m_sub, n:n_sub, aa:aa_sub, x:x_sub,
                 bb:bb_sub, cc:cc_sub}, assumptions=assumptions)
        else:
            return reduction_left.specialize(
                {l:l_sub, m:m_sub, n:n_sub, aa:aa_sub, x:x_sub,
                 bb:bb_sub, cc:cc_sub}, assumptions=assumptions)


    def single_elem_substitution(self, elem=None, idx=None, sub_elem=None,
                                 assumptions=USE_DEFAULTS):
        '''
        Deduce that this enum Set expression is equal to a Set
        in which the element specified either by elem or by the
        position idx has been replaced with sub_elem. The deduction
        depends on the sub_elem being equal to the replace elem.
        If elem specified in the form elem='elem', method attempts to
        substitute for the 1st occurrence of elem; if elem=['elem',n],
        method attempts to substitute for the nth occurrence of elem.
        If both elem and idx are specified, the elem arg is ignored.
        Examples: Let S = Set(a, b, a, b, a, c). Then
        S.single_elem_substitution() gives error;
        S.single_elem_substitution(elem=b, sub_elem=four,
                                   assumptions=[Equals(b, four)])
            gives |- S = {a, 4, a, b, a, c};
        S.single_elem_substitution(elem=[b, 2], sub_elem=four,
                                   assumptions=[Equals(b, four)])
            gives |- S = {a, b, a, 4, a, c};
        S.single_elem_substitution(idx=3, sub_elem=four,
                                   assumptions=[Equals(b, four)])
            gives |- S = {a, b, a, 4, a, c};
        '''
        # First, a quick check on elem, idx, and sub_elem arguments
        if elem == None and idx == None:
            raise ValueError("single_elem_substitution() method requires "
                             "the specification of element (elem=) or "
                             "element index (idx=) candidate for "
                             "substitution.")
        if sub_elem == None:
            raise ValueError("single_elem_substitution() method missing "
                             "sub_elem argument. Must specify the replacement "
                             "value using argument 'sub_elem='.")

        set_length = len(self.operands)

        # if user has specified position index idx,
        # check for validity and use idx if possible
        if idx is not None and (idx < -set_length or idx >= set_length):
            raise IndexError("Index specification idx = {0} is out of bounds. "
                             "Need {1} ≤ idx ≤ {2}.".
                             format(idx,-set_length, set_length-1))
        if idx is not None:
            # we already checked for valid idx, so
            # transform any wrap-around indexing for simplicity
            if idx < 0: idx = set_length+idx
            elem = self.operands[idx]

        # Designate which one of (possibly) multiple copies of the
        # elem we want to replace -- default is 1st location:
        which_elem = 1  

        if idx==None:
            # We must have had an elem specified
            if isinstance(elem, list): # elem = [x, n]
                which_elem = elem[1]   # which_elem = n
                elem = elem[0]         # elem = x
                if which_elem < 1 or which_elem > len(self.operands):
                    raise ValueError(
                            "In specifying the elem to be replaced in the "
                            "call to Set.single_elem_substitution(), it "
                            "doesn't appear to make sense to specify instance "
                            "#{0} of the element {1} in the set of elements "
                            "{2}.".format(which_elem, elem, self.operands))
            # find indice(s) of elem in Set
            elem_indices = (
                [i for i, j in enumerate(self.operands) if j == elem])
            if len(elem_indices) >= which_elem and which_elem > 0:
                idx = elem_indices[which_elem - 1]
            else:
                raise ValueError(
                        "single_elem_substitution() method looked for "
                        "{0} instance(s) of the elem '{1}' in the set {2} "
                        "but found only {3} instance(s). The elem '{1}' does "
                        "not appear to exist in the original set with "
                        "sufficient multiplicity.".
                        format(which_elem, elem, self.operands,
                               len(elem_indices)))

        # We should now have a valid idx indicating the index of the
        # set item to be replaced, either because it was explicitly
        # supplied or because it was derived from the elem argument

        # We deduce the desired equality by specializing the
        # equalElementEquality theorem from the enumeration context
        from ._theorems_ import equalElementEquality
        # --- Organize the specialization mapping info.
        from proveit.number import num
        m, n, aa, b, cc, d = equalElementEquality.allInstanceVars()
        # --- Break the set into [ ]+[idx]+[ ].
        m_sub, n_sub = (num(idx), num(set_length - idx - 1))
        aa_sub, b_sub, cc_sub, d_sub = (
                list(self.operands)[0:idx],
                list(self.operands)[idx],
                list(self.operands)[idx + 1:],
                sub_elem)
        # --- Specialize and return.
        return equalElementEquality.specialize(
            {m:m_sub, n:n_sub, aa:aa_sub, b:b_sub, cc:cc_sub, d:d_sub},
            assumptions=assumptions)

    def elem_substitution(self, elem=None, sub_elem=None,
                          assumptions=USE_DEFAULTS):
        '''
        Deduce that this enum Set expression is equal to the Set
        obtained when every instance of elem in self is replaced by the
        sub_elem. The deduction depends on the sub_elem being equal to
        the elem it is replacing.
        Examples: Let S = Set(a, b, a, b, a, c). Then
        S.elem_substitution() gives ERROR;
        S.elem_substitution(elem=d, sub_elem=two,
                            assumptions=[Equals(d, two)] gives ERROR;
        S.elem_substitution(elem=b, sub_elem=four,
                            assumptions=[Equals(b, four)])
            gives |- S = {a, 4, a, 4, a, c};
        S.single_elem_substitution(elem=a, sub_elem=two,
                                   assumptions=[Equals(a, two)])
            gives |- S = {2, b, 2, b, 2, c};
        S.single_elem_substitution(elem=c, sub_elem=d,
                                   assumptions=[Equals(c, d)])
            gives |- S = {a, b, a, b, a, d};
        '''
        # First, a quick check on elem and sub_elem arguments
        if elem == None or sub_elem == None:
            raise ValueError("Set.elem_substitution() method requires "
                             "the specification of the element to be replaced "
                             "and the requested substitution value, but "
                             "found elem={0} and sub_elem={1}.".
                             format(elem, sub_elem))
        
        if elem not in self.operands:
            raise ValueError("In calling the Set.elem_substitution() method, "
                             "the element '{0}' to be replaced does not "
                             "appear to exist in the original set {1}.".
                             format(elem, self))

        # count the number of elems to replace with the sub_elem
        self_list = list(self.operands)
        num_elems_to_replace = self_list.count(elem)

        from proveit import TransRelUpdater
        eq = TransRelUpdater(self, assumptions)

        expr = self
        while num_elems_to_replace > 0:
            expr = eq.update(expr.single_elem_substitution(
                    elem=elem, sub_elem=sub_elem, assumptions=assumptions))
            num_elems_to_replace -= 1

        return eq.relation


    # ----------------- #
    # Utility Functions #
    # ----------------- #

    def _check_subset_indices_weak(
            self, valid_indices_list, subset_indices_list,
            proper_subset = False):
        '''
        A minimal check that indices in subset_indices_list form a
        valid subset of the valid_indices_list, which requires only
        that the indices in subset_indices_list appear in the
        valid_indices_list. Multiplicity is not an issue (for example,
        subset_indices_list could be [0, 1, 2, 1] and valid_indices_list
        could be [0, 1, 2, 3]). If proper_subset flag set to True, the
        subset_indices_list with multiplicities removed must have
        strictly fewer elements than the valid_indices_list with
        multiplicities removed.
        LATER: allow negative indices?
        '''

        valid_indices_set = set(valid_indices_list)
        subset_indices_set =  set(subset_indices_list)
        unexpected_indices_set = subset_indices_set - valid_indices_set
        if len(unexpected_indices_set) != 0:
            raise IndexError(
                    "Index or indices out of bounds: {0}. Subset indices "
                    "should be elements of {1}.".
                    format(unexpected_indices_set,valid_indices_set))
        # if we made it this far and proper_subset = True,
        # confirm that the subset indices are compatible with a proper
        # subset instead of an improper subset
        if proper_subset and len(subset_indices_set) == len(valid_indices_set):
            raise ValueError("The subset indices are not compatible with a "
                             "proper subset (too many elements).")


    def _check_subset_indices(self, valid_indices_list, subset_indices_list,
                              proper_subset = False):
        '''
        Checks if indices in subset_indices_list form a valid subset of
        the valid_indices_list, which requires that the indices in
        subset_indices_list have multiplicity <= 1 and values i such
        that i is an element of valid_indices_list. If proper_subset
        flag set to True, the subset_indices_list must have strictly
        fewer elements than valid_indices_list.
        LATER: allow negative indices?
        '''

        valid_indices_set = set(valid_indices_list)
        # allowed_indices_set = set(range(0, len(self.operands)))
        subset_indices_set =  set(subset_indices_list)
        unexpected_indices_set = subset_indices_set - valid_indices_set
        if len(unexpected_indices_set) != 0:
            raise IndexError("Index or indices out of bounds: {0}. "
                             "subset indices i should satisfy "
                             "0 ≤ i ≤ {1}.".
                             format(unexpected_indices_set,
                                    len(valid_indices_set) - 1))
        if len(subset_indices_list) > len(subset_indices_set):
            # we have repeated indices, so let's find them to use in
            # feedback/error message
            repeated_indices_set = set()
            for elem in subset_indices_set:
                if subset_indices_list.count(elem) > 1:
                    repeated_indices_set.add(elem)
            raise ValueError("The subset_indices specification contains "
                             "repeated indices, with repeated index or "
                             "indices: {}. Each index value should appear at "
                             "most 1 time.".format(repeated_indices_set))
        # if we made it this far and proper_subset = True,
        # confirm that the subset indices are compatible with a proper
        # subset instead of an improper subset
        if proper_subset and len(subset_indices_set) == len(valid_indices_set):
            raise ValueError("The subset indices are not compatible with a "
                             "proper subset (too many elements).")


# Register these expression equivalence methods:
InnerExpr.register_equivalence_method(Set, 'permutation', 'permuted', 'permute')
InnerExpr.register_equivalence_method(Set, 'permutation_move', 'moved', 'move')
InnerExpr.register_equivalence_method(Set, 'reduction', 'reduced', 'reduce')



