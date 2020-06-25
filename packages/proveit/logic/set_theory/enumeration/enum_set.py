from proveit import Literal, Operation, ExprTuple, USE_DEFAULTS
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

    # this has been renamed to permutation_move;
    # and permutationGeneral has been renamed as permutation
    # def permutation(self, initIdx=None, finalIdx=None,
    #                 assumptions=USE_DEFAULTS):
    #     '''
    #     Deduce that this Set expression is set-equivalent to a Set
    #     in which the element at index initIdx has been moved to
    #     finalIdx. For example, {a, b, c, d} = {a, c, b, d} via
    #     initIdx = 1 (i.e. 'b') and finalIdx = -2. In traditional
    #     cycle notation, this corresponds to an index-based cycle
    #     (initIdx, initIdx+1, … finalIdx) where
    #     0 ≤ initIdx ≤ finalIdx ≤ n - 1 for a set of size n.
    #     TO BE REPLACED WITH ALTERNATELY-NAMED
    #     permutationSimple() BELOW. Maintained here temporarily.
    #     '''
    #     from ._theorems_ import (binaryPermutation, leftwardPermutation,
    #                              rightwardPermutation)
    #     return apply_commutation_thm(self, initIdx, finalIdx, binaryPermutation,
    #                                  leftwardPermutation, rightwardPermutation,
    #                                  assumptions)

    def permutation_move(self, initIdx=None, finalIdx=None,
                         assumptions=USE_DEFAULTS):
        '''
        change to permutationMove (using move as the verb)
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

    def deduceEnumSubsetEqOld(self, subset_indices=None,
                         assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression has as an improper subset the
        set specified by the indices in subset_indices list.
        For example,
        {a, b, c, d}.deduceEnumSubsetEq(subset_indices=[1, 3]) returns
        |– {b, d} subsetEq {a, b, c, d}.
        This approach assumes we are not dealing with multisets
        (or "bags"), but often works with multisets anyway.
        See the new and improved version of this method below,
        which accepts a Set() for the subset param.
        '''

        from ._theorems_ import subsetEqOfSuperset
        from proveit._common_ import m, n, aa, bb
        from proveit.number import num

        # check validity of provided subset_indices:
        valid_indices_list = list(range(0, len(self.operands)))
        self._check_subset_indices(valid_indices_list, subset_indices)

        full_indices_list = list(range(0, len(self.operands)))

        # construct the complement of the subset indices
        # avoiding using sets to preserve order just in case
        remaining_indices = list(full_indices_list) # clone
        for elem in subset_indices:
            remaining_indices.remove(elem)

        new_order = subset_indices + remaining_indices
        # find superset permutation needed for thm application
        supersetPermRelation = generic_permutation(self, new_order, assumptions)
        # construct the desired list of subset elems
        desired_subset_list = []
        for elem in subset_indices:
            desired_subset_list.append(self.operands[elem])
        # construct the desired complement list of elems
        desired_complement_list = []
        for elem in remaining_indices:
            desired_complement_list.append(self.operands[elem])
        # borrowed the following organization from apply_commutation_thm
        m, n, a, b = subsetEqOfSuperset.allInstanceVars()
        a_sub, b_sub = (desired_subset_list, desired_complement_list)
        m_sub, n_sub = num(len(a_sub)), num(len(b_sub))
        subset_of_permuted_superset = subsetEqOfSuperset.specialize(
                {m:m_sub, n:n_sub, a:a_sub, b:b_sub},
                assumptions=assumptions)

        return supersetPermRelation.subLeftSideInto(subset_of_permuted_superset)

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
        CURRENTLY this approach interprets the subset input param as a
        possible multiset and then treats it as such! But that needs
        to change! And what about empty sets?
        '''

        from proveit.logic import Set

        # Before bothering with much processing, quickly check that:
        # (1) user has specified subset_indices OR subset but not both;
        # (2) subset specification has the correct form;
        # (3) subset_indices are plausible.
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
        print("self_list: {}".format(self_list))                                # for testing; delete later

        # If subset has been specified, check that it is a
        # plausible subset (it should only have elements found in
        # the original Set)
        if subset is not None:
            subset_list = list(subset.operands)
            print("subset_list = {}".format(subset_list))                       # for testing; delete later
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

        valid_indices_list = list(range(0, len(self.operands)))
        subset_list_from_indices = []
        if subset_indices is not None:
            # We must have had subset=None
            self._check_subset_indices(valid_indices_list, subset_indices)
            subset_list_from_indices = [self_list[i] for i in subset_indices]
            print("subset_list_from_indices: {}".                               # for testing; delete later
                  format(subset_list_from_indices))                             # for testing; delete later
            subset_from_indices = Set(*subset_list_from_indices)
            print("subset_from_indices: {}".format(subset_from_indices))        # for testingl delete later
            subset = subset_from_indices
            print("subset is derived from indices and is now: {}".              # for testingl delete later
                  format(subset))                                               # for testingl delete later

        # Derive the reduced form of the self Set. We could have done
        # this earlier, but delayed until after param checking.
        # The eventual subset relationship will be based on the
        # reduced forms of the specified Sets.
        self_to_support_kt = self.reduction(assumptions=assumptions)
        print("self_to_support_kt: {}".format(self_to_support_kt))              # for testing; delete later
        self_reduced = self_to_support_kt.rhs
        self_reduced_list = list(self_reduced.operands)
        print("self_reduced: {}".format(self_reduced))                          # for testing; delete later
        print("self_reduced_list: {}".format(self_reduced_list))                # for testing; delete later

        



        from ._theorems_ import subsetEqOfSuperset
        from proveit._common_ import m, n, aa, bb
        from proveit.number import num

        # If we make it this far we should have an explicit subset Set,
        # either explicitly provided or derived from the
        # subset_indices. We now derive the reduced form of the subset
        # Set. The eventual subset relationship will be based on the
        # reduced forms of the specified Sets.
        subset_to_support_kt = subset.reduction(assumptions=assumptions)
        print("subset_to_support_kt: {}".format(subset_to_support_kt))          # for testing; delete later
        subset_reduced = subset_to_support_kt.rhs
        print("subset_reduced: {}".format(subset_reduced))                      # for testing; delete later
        subset_reduced_list = list(subset_reduced.operands)
        print("subset_reduced_list: {}".format(subset_reduced_list))            # for testing; delete later
        

        # For convenience, convert the subset_reduced_list to indices
        # of the self_reduced_list. Because of earlier checks, the
        # subset_reduced_list should not contain any items not also
        # contained in self_reduced_list.
        subset_reduced_indices_list = (
            [self_reduced_list.index(elem) for elem in subset_reduced_list])
        print("subset_reduced_indices_list: {}".format(subset_reduced_indices_list))      # for testing; delete later



        # if we make it this far and we have a subset provided,
        # convert the provided subset to indices of the superset to
        # make use of index-based machinery
        subset_indices_list = []
        if subset is not None:
            superset_list = list(self.operands)
            superset_remaining_list = list(self.operands)
            subset_list = list(subset.operands)
            for elem in subset_list:
                if elem in superset_remaining_list:
                    superset_remaining_list.remove(elem)
                    tempIdx = superset_list.index(elem)
                    while tempIdx in subset_indices_list:
                        tempIdx = superset_list.index(elem, tempIdx + 1)
                    subset_indices_list.append(tempIdx)
                else:
                    raise ValueError("Element {0} of proposed subset does not "
                                     "appear in superset {1} with sufficient "
                                     "multiplicity.".
                                     format(elem, superset_list))

        # if subset is not None:
        #     # use the Set-based generated subset indices
        #     subset_indices = list(subset_indices_list)
        #     # else use the user-provided indices

        # full_indices_list = list(range(0, len(self.operands)))

        # # construct the complement of the subset indices
        # # avoiding using sets to preserve order just in case
        # remaining_indices = list(full_indices_list) # clone
        # for elem in subset_indices:
        #     remaining_indices.remove(elem)

        # new_order = subset_indices + remaining_indices
        # # find superset permutation needed for thm application
        # supersetPermRelation = generic_permutation(self, new_order, assumptions)
        # # construct the desired list of subset elems
        # desired_subset_list = []
        # for elem in subset_indices:
        #     desired_subset_list.append(self.operands[elem])
        # # construct the desired complement list of elems
        # desired_complement_list = []
        # for elem in remaining_indices:
        #     desired_complement_list.append(self.operands[elem])
        # # organize info for theorem specialization
        # m, n, a, b = subsetEqOfSuperset.allInstanceVars()
        # a_sub, b_sub = (desired_subset_list, desired_complement_list)
        # m_sub, n_sub = num(len(a_sub)), num(len(b_sub))
        # subset_of_permuted_superset = subsetEqOfSuperset.specialize(
        #         {m:m_sub, n:n_sub, a:a_sub, b:b_sub},
        #         assumptions=assumptions)
        
        # return supersetPermRelation.subLeftSideInto(
        #         subset_of_permuted_superset.innerExpr().rhs
        #         )

        if subset is not None:
            # use the Set-based generated subset indices
            subset_indices = list(subset_indices_list)
            # else use the user-provided indices

        full_indices_list = list(range(0, len(self_reduced_list)))

        # construct the complement of the subset indices
        # avoiding using sets to preserve order just in case
        remaining_indices = list(full_indices_list) # clone
        for elem in subset_reduced_indices_list:
            remaining_indices.remove(elem)

        new_order = subset_reduced_indices_list + remaining_indices
        # find superset permutation needed for thm application
        supersetPermRelation = generic_permutation(
                self_reduced, new_order, assumptions)
        # construct the desired list of subset elems
        desired_subset_list = subset_reduced_list
        # for elem in subset_indices:
        #     desired_subset_list.append(self.operands[elem])
        # construct the desired complement list of elems
        desired_complement_list = []
        for elem in remaining_indices:
            desired_complement_list.append(self_reduced_list[elem])
        # organize info for theorem specialization
        m, n, a, b = subsetEqOfSuperset.allInstanceVars()
        a_sub, b_sub = (desired_subset_list, desired_complement_list)
        m_sub, n_sub = num(len(a_sub)), num(len(b_sub))
        subset_of_permuted_superset = subsetEqOfSuperset.specialize(
                {m:m_sub, n:n_sub, a:a_sub, b:b_sub},
                assumptions=assumptions)
        # We now have reduced_subset \subseteq reduced_superset
        # Now, replace permuted superset with unpermuted reduced
        # superset:
        reduced_subset_of_reduced_superset = (
                supersetPermRelation.subLeftSideInto(
                        subset_of_permuted_superset.innerExpr().rhs))
        # Then, replace reduced superset with original superset:
        reduced_subset_of_orig_superset = (
                self_to_support_kt.subLeftSideInto(
                        reduced_subset_of_reduced_superset))
        # Finally, replace the reduced subset with original subset:
        orig_subset_of_orig_superset = (
                subset_to_support_kt.subLeftSideInto(
                        reduced_subset_of_orig_superset))
        
        return orig_subset_of_orig_superset


    def deduceEnumProperSubset(self, subset_indices=None,
                               assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression has as a proper subset the
        set specified by the indices in the subset_indices list.
        For example,
        {a, b, c, d}.deduceEnumSubset(subset_indices=[1, 3]) returns
        |– {b, d} subset {a, b, c, d}.
        This approach assumes we are not dealing with multisets
        (or "bags").
        '''

        from ._theorems_ import properSubsetOfSuperset
        from proveit._common_ import m, n, aa, bb
        from proveit.number import num

        # check validity of provided subset_indices:
        valid_indices_list = list(range(0, len(self.operands)))
        self._check_subset_indices(valid_indices_list, subset_indices,
                                   proper_subset = True)

        full_indices_list = list(range(0, len(self.operands)))

        # construct the complement of the subset indices
        # avoiding using sets to preserve order just in case
        remaining_indices = list(full_indices_list) # clone
        for elem in subset_indices:
            remaining_indices.remove(elem)

        new_order = subset_indices + remaining_indices
        # find superset permutation needed for thm application
        supersetPermRelation = generic_permutation(self, new_order, assumptions)
        # construct the desired list of subset elems
        desired_subset_list = []
        for elem in subset_indices:
            desired_subset_list.append(self.operands[elem])
        # construct the desired complement list of elems
        desired_complement_list = []
        for elem in remaining_indices:
            desired_complement_list.append(self.operands[elem])
        # borrowed the following organization from apply_commutation_thm
        m, n, a, b = properSubsetOfSuperset.allInstanceVars()
        a_sub, b_sub = (desired_subset_list, desired_complement_list)
        m_sub, n_sub = num(len(a_sub)), num(len(b_sub))
        subset_of_permuted_superset = properSubsetOfSuperset.specialize(
                {m:m_sub, n:n_sub, a:a_sub, b:b_sub},
                assumptions=assumptions)

        return supersetPermRelation.subLeftSideInto(subset_of_permuted_superset)

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
        Created 02/07/2020 by wdc.
        Last modified 02/07/2020 by wdc:
            Creation; established input param checking
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


    # ----------------- #
    # Utility Functions #
    # ----------------- #

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



