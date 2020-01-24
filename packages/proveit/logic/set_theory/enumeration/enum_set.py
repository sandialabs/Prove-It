from proveit import Literal, Operation, ExprTuple, USE_DEFAULTS
from proveit.abstract_algebra.generic_methods import apply_permutation_thm
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

    def permutation(self, initIdx=None, finalIdx=None,
                    assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression is set-equivalent to a Set
        in which the element at index initIdx has been moved to
        finalIdx. For example, {a, b, c, d} = {a, c, b, d} via
        initIdx = 1 (i.e. 'b') and finalIdx = -2. In traditional
        cycle notation, this corresponds to an index-based cycle
        (initIdx, initIdx+1, … finalIdx) where
        0 ≤ initIdx ≤ finalIdx ≤ n - 1 for a set of size n.
        TO BE REPLACED WITH ALTERNATELY-NAMED
        permutationSimple() BELOW. Maintained here temporarily.
        '''
        from ._theorems_ import (binaryPermutation, leftwardPermutation,
                                 rightwardPermutation)
        return apply_commutation_thm(self, initIdx, finalIdx, binaryPermutation,
                                     leftwardPermutation, rightwardPermutation,
                                     assumptions)

    def permutationSimple(self, initIdx=None, finalIdx=None,
                          assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression is set-equivalent to a Set
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

    def permutationGeneral(self, new_order=None, cycles=None,
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

    def deduceEnumSubsetEq(self, subset_indices=None,
                         assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression has as an improper subset the
        set specified by the indices in subset_indices list.
        For example,
        {a, b, c, d}.deduceEnumSubsetEq(subset_indices=[1, 3]) returns
        |– {b, d} subsetEq {a, b, c, d}.
        This approach assumes we are not dealing with multisets
        (or "bags"), but often works with multisets anyway.
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

    def deduceEnumSubsetEqAlt(self, subset_indices=None, subset=None,
                         assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression has as an improper subset the
        set specified by either the indices in subset_indices list or
        the Set() specified by subset.
        For example, both
        {a, b, c, d}.deduceEnumSubsetEq(subset_indices=[1, 3]) and
        {a, b, c, d}.deduceEnumSubsetEq(subset=Set(b, d))
        return |– {b, d} subsetEq {a, b, c, d}.
        This approach assumes we are not dealing with multisets
        (or "bags"). BUT it might still work with multisets!
        This alt version is temporary to develop param input allowing
        the specification of a subset itself rather than just indices.
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
        if not subset_indices is None and not subset is None:
            raise ValueError("Need to specify the desired subset by "
                             "specifying the list of indices (subset_indices) "
                             "OR an actual subset, but NOT both.")

        # if subset has been specified, check that:
        # (1) it is a valid Set()
        # (2) has a valid cardinality
        # (3) then convert to an list of indices
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

        # if we make it this far and we have a subset provided
        # convert to indices to make use of previously-established
        # machinery
        if subset is not None:
            superset_list = list(self.operands)
            superset_remaining_list = list(self.operands)
            subset_list = list(subset.operands)
            subset_indices_list = []
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
            print("subset_indices_list = {}".format(subset_indices_list))       # for testing; delete later


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


    def deduceEnumProperSubset(self, subset_indices=None,
                         assumptions=USE_DEFAULTS):
        '''
        Deduce that this Set expression has as a proper subset the
        set specified by the indices in subset_indices list.
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



