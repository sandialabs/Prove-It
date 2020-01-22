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
        {a, b, c, d}.deduceEnumSubset(subset_indices=[1, 3]) returns
        |– {b, d} subsetEq {a, b, c, d}.
        '''

        from ._theorems_ import subsetEqOfSuperset
        from proveit._common_ import m, n, aa, bb
        from proveit.number import num

        # check validity of provided subset_indices: 
        # (1) each index i needs to be 0 ≤ i ≤ n-1;
        # (2) cannot have repeated indices
        # can eventually move this code portion to separate method
        # later also allow negative indices to be used
        allowed_indices_set = set(range(0, len(self.operands)))
        subset_indices_set =  set(subset_indices)
        unexpected_indices_set = subset_indices_set - allowed_indices_set
        if len(unexpected_indices_set) != 0:
            raise IndexError("Index or indices out of bounds: {0}. "
                             "subset_indices should be a list of indices "
                             "i such that 0 ≤ i ≤ {1}.".
                             format(unexpected_indices_set,
                                    len(self.operands) - 1))
        if len(subset_indices) > len(subset_indices_set):
            # we have repeated indices, so let's find them for feedback
            repeated_indices_set = set()
            for elem in subset_indices_set:
                if subset_indices.count(elem) > 1:
                    repeated_indices_set.add(elem)

            raise ValueError("The subset_indices specification contains "
                             "repeated indices, with repeated index or indices: "
                             "{}. Each index value should appear at most "
                             "1 time.".format(repeated_indices_set))

        # omitting checking of arguments for now
        # assume subset_indices are correct
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


