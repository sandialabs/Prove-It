from proveit import Literal, Operation, ExprTuple, USE_DEFAULTS
# from proveit.abstract_algebra.generic_methods import apply_permutation_thm
from proveit.abstract_algebra.generic_methods import (
        apply_commutation_thm, generic_permutation)

class Set(Operation):
    '''
    Defines an enumerated set (i.e. a set with explicitly-listed
    elements). For example, one could use Set(one, two, three) to
    produce the enumerated set {1, 2, 3} or Set(a, b, a) to produce
    the enumerated set {a, b, a}.
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
        PERHAPS CALL THIS ONE just permutation
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
        Currently this approach interprets the subset input param as a
        possible multiset and then treats it as such! But that needs
        to change!
        '''

        from ._theorems_ import subsetEqOfSuperset
        from proveit._common_ import m, n, aa, bb
        from proveit.number import num
        from proveit.logic import Set

        # check that user has specified subset_indices OR subset
        # but NOT both
        if subset_indices is None and subset is None:
            raise ValueError("Need to specify the desired subset by "
                             "specifying the list of indices (subset_indices) "
                             "OR an actual subset (in the form of an "
                             "enumerated set using Set()).")
        if subset_indices is not None and subset is not None:
            raise ValueError("Need to specify the desired subset by "
                             "specifying the list of indices (subset_indices) "
                             "OR an actual subset, but NOT both.")

        # if subset has been specified, check that:
        # (1) it is a valid Set()
        # (2) has a valid cardinality
        if subset is not None and not isinstance(subset, Set):
            raise ValueError("Specified subset {} does not appear to be a "
                             "valid Set object.".format(subset))
        if (isinstance(subset, Set) and 
            len(subset.operands) > len(self.operands)):
            raise ValueError("Specified subset {0} with length {1} appears to "
                             "be too large to be a subset of the superset "
                             "{2} with length {3}.".
                             format(subset, len(subset.operands),
                                self.operands, len(self.operands)))

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

        if subset is not None:
            # use the Set-based generated subset indices
            subset_indices = list(subset_indices_list)
            # else use the user-provided indices

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
        # organize info for theorem specialization
        m, n, a, b = subsetEqOfSuperset.allInstanceVars()
        a_sub, b_sub = (desired_subset_list, desired_complement_list)
        m_sub, n_sub = num(len(a_sub)), num(len(b_sub))
        subset_of_permuted_superset = subsetEqOfSuperset.specialize(
                {m:m_sub, n:n_sub, a:a_sub, b:b_sub},
                assumptions=assumptions)
        
        return supersetPermRelation.subLeftSideInto(
                subset_of_permuted_superset.innerExpr().rhs
                )


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

    def reduction_elem(self, elem=None, idx=None):
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
            creation; established input param checking
        '''
        n = len(self.operands)

        # if user has specified position index idx, use that
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
                                 "idx={1} occurs just once in the enum set "
                                 "and thus cannot be eliminated.".
                                 format(elem, idx))

        if idx is None and elem is not None:
            # find index of 2nd occurrence of elem, if it exists
            # first gen enumerated list of those repeated elems
            idx_list_of_elem = (
                [i for i,j in enumerate(self.operands) if j == elem])
            if len(idx_list_of_elem) < 2:
                raise ValueError("Specified element '{0}' appears just {1} "
                                 "time(s) in the set and thus cannot be "
                                 "eliminated.".
                                 format(elem, len(idx_list_of_elem)))
            else:
                idx = idx_list_of_elem[1]

        return "The idx value is: " + str(idx)


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



