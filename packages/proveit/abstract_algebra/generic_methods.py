from proveit import USE_DEFAULTS, singleOrCompositeExpression


def apply_commutation_thm(expr, initIdx, finalIdx, binaryThm, leftwardThm,
                          rightwardThm, assumptions=USE_DEFAULTS):

    from proveit.logic import Equals, Set, SetEquiv
    from proveit.number import num

    # check validity of default usage of indices
    if initIdx is None or finalIdx is None:
        if len(expr.operands) != 2:
            raise IndexError("You may use default 'initIdx' or "
                             "'finalIdx' values when applying "
                             "commutation only if your set or "
                             "set-like object contains exactly 2 "
                             "elements.")
        if initIdx is not finalIdx:
            raise IndexError("When applying commutation, you must "
                             "either supply both 'initIdx' and "
                             "'finalIdx' or supply neither (allowed "
                             "when there are only 2 elements)")
        initIdx, finalIdx = 0, 1 # defaults when there are 2 operands

    # transform any wrap-around indexing for simplicity
    if initIdx < 0: initIdx = len(expr.operands)+initIdx
    if finalIdx < 0: finalIdx = len(expr.operands)+finalIdx

    # check validity of supplied index values
    if initIdx >= len(expr.operands):
        raise IndexError("'initIdx' = {0} is out of range. Should "
                         "have 0 ≤ initIdx ≤ {1}.".
                         format(initIdx, len(expr.operands) - 1))
    if finalIdx >= len(expr.operands):
        raise IndexError("'finalIdx' = {0} is out of range. Should "
                         "have 0 ≤ finalIdx ≤ {1}.".
                         format(finalIdx, len(expr.operands) - 1))

    # trivial commutation (i.e. non-commutation)
    # but we need to distinguish SetEquiv from Equals
    if initIdx==finalIdx:
        if isinstance(expr, Set):
            return SetEquiv(expr, expr).prove()
        return Equals(expr, expr).prove()

    # number of operands or elements = 2
    if len(expr.operands)==2 and set([initIdx, finalIdx]) == {0, 1}:
        A, B = binaryThm.allInstanceVars()
        return binaryThm.specialize({A:expr.operands[0], B:expr.operands[1]},
                                    assumptions=assumptions)

    # number of operands is ≥ 3
    if initIdx < finalIdx:
        thm = rightwardThm
        l, m, n, A, B, C, D = thm.allInstanceVars()
        Asub, Bsub, Csub, Dsub = (
            expr.operands[:initIdx], expr.operands[initIdx],
            expr.operands[initIdx+1:finalIdx+1], expr.operands[finalIdx+1:])
        lSub, mSub, nSub = num(len(Asub)), num(len(Csub)), num(len(Dsub))
    else:
        thm = leftwardThm
        l, m, n, A, B, C, D = thm.allInstanceVars()
        Asub, Bsub, Csub, Dsub = expr.operands[:finalIdx], expr.operands[finalIdx:initIdx], expr.operands[initIdx], expr.operands[initIdx+1:]
        lSub, mSub, nSub = num(len(Asub)), num(len(Bsub)), num(len(Dsub))
    return thm.specialize(
        {l:lSub, m:mSub, n:nSub, A:Asub, B:Bsub, C:Csub, D:Dsub},
        assumptions=assumptions)

def apply_association_thm(expr, startIdx, length, thm, assumptions=USE_DEFAULTS):
    from proveit.logic import Equals
    from proveit.number import num
    beg, end = startIdx, startIdx+length
    if beg < 0: beg = len(expr.operands)+beg # use wrap-around indexing
    if not length >= 2:
        raise IndexError ("The 'length' must be 2 or more when "
                          "applying association.")
    if end > len(expr.operands):
        raise IndexError("'startIdx+length' out of bounds: %d > %d."%(
                         end, len(expr.operands)))
    if beg==0 and end==len(expr.operands):
        # association over the entire range is trivial:
        return Equals(expr, expr).prove() # simply the self equality
    l, m, n, AA, BB, CC = thm.allInstanceVars()
    return thm.specialize({l :num(beg), m:num(end - beg), n: num(len(expr.operands) - end), AA:expr.operands[:beg], BB:expr.operands[beg : end], CC: expr.operands[end :]}, assumptions=assumptions)

def apply_disassociation_thm(expr, idx, thm=None, assumptions=USE_DEFAULTS):
    from proveit.number import num
    if idx < 0: idx = len(expr.operands)+idx # use wrap-around indexing
    if idx >= len(expr.operands):
        raise IndexError("'idx' out of range for disassociation")
    if not isinstance(expr.operands[idx], expr.__class__):
        raise ValueError("Expecting %d index of %s to be grouped (i.e., a "
                         "nested expression of the same type)"
                         %(idx, str(expr)))
    l, m, n, AA, BB, CC = thm.allInstanceVars()
    length = len(expr.operands[idx].operands)
    return thm.specialize({l:num(idx), m:num(length), n: num(len(expr.operands) - idx - 1), AA:expr.operands[:idx], BB:expr.operands[idx].operands, CC:expr.operands[idx+1:]}, assumptions=assumptions)

def apply_permutation_thm(expr, initIdx, finalIdx, binaryThm, leftwardThm,
                          rightwardThm, assumptions=USE_DEFAULTS):
    '''
    UNDER CONSTRUCTION
    '''
    from proveit.logic import SetEquiv
    # Some initial print statements for testing
    print("Entering apply_permutation_thm.")
    print("    initIdx = {}".format(initIdx))
    print("    finalIdx = {}".format(finalIdx))
    print("    assumptions = {}".format(assumptions))

    # check validity of supplied indices in terms of defaults
    if initIdx is None or finalIdx is None:
        if len(expr.operands) != 2:
            raise IndexError("You may use default 'initIdx' or "
                             "'finalIdx' values when applying "
                             "permutation only if your set or "
                             "set-like object contains exactly 2 "
                             "elements.")
        if initIdx is not finalIdx:
            raise IndexError("When applying permutation, you must "
                             "either supply both 'initIdx' and "
                             "'finalIdx' or supply neither (allowed "
                             "when there are only 2 elements)")
        initIdx, finalIdx = 0, 1  # defaults when there are 2 elements

    # acknowledge any wrap-around indexing; transform for simplicity
    if initIdx < 0: initIdx = len(expr.operands)+initIdx
    if finalIdx < 0: finalIdx = len(expr.operands)+finalIdx

    # check validity of supplied index values
    if initIdx >= len(expr.operands):
        raise IndexError("'initIdx' = {0} is out of range. Should "
                         "have 0 ≤ initIdx ≤ {1}.".
                         format(initIdx, len(expr.operands) - 1))
    if finalIdx >= len(expr.operands):
        raise IndexError("'finalIdx' = {0} is out of range. Should "
                         "have 0 ≤ finalIdx ≤ {1}.".
                         format(finalIdx, len(expr.operands) - 1))

    # trivial permutation
    if initIdx==finalIdx:
        return SetEquiv(expr, expr).prove()

    # Set or set-like object with cardinality = 2
    if len(expr.operands)==2 and set([initIdx, finalIdx]) == {0, 1}:
        A, B = binaryThm.allInstanceVars()
        return binaryThm.specialize({A:expr.operands[0], B:expr.operands[1]},
                                    assumptions=assumptions)
    
    # 
    if initIdx < finalIdx:
        thm = rightwardThm
        print("rightwardThm = ".format(thm))
        print("rightwardThm.allInstanceVars() = ".format(thm.allInstanceVars()))
        # l, m, n, A, B, C, D = rightwardThm.allInstanceVars()
        # Asub, Bsub, Csub, Dsub = expr.operands[:initIdx], expr.operands[initIdx], expr.operands[initIdx+1:finalIdx+1], expr.operands[finalIdx+1:]
        # lSub, mSub, nSub = num(len(Asub)), num(len(Csub)), num(len(Dsub))
    

    return expr

def groupCommutation(expr, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
    '''
    Derive a commutation equivalence on a group of multiple operands by
    associating them together first.  If 'dissassociate' is true, the
    group will be disassociated at end. For example, the following call:
    Or(A,B,C,D).groupCommutation(0, 1, length=2,
                                 assumptions=inBool(A,B,C,D))
    essentially goes through the following steps:
    (1) associates 2 elements (i.e. length = 2) starting at index 0 to
        obtain (A V B) V C V D
    (2) removes the element to be commuted to obtain C V D
    (2) inserts the element to be commuted at the desire index to
        obtain C V (A V B) V D
    (3) then disassociates to obtain C V A V B V D
    (4) eventually producing the output:
    {A in Bool, ..., D in Bool} |- (A V B V C V D) = (C V A V B V D)
    '''
    from proveit import TransRelUpdater

    if initIdx < 0: initIdx = len(expr.operands)+initIdx # use wrap-around indexing
    if finalIdx < 0: finalIdx = len(expr.operands)+finalIdx # use wrap-around indexing
    if length==1:
        return expr.commutation(initIdx, finalIdx, assumptions=assumptions)

    eq = TransRelUpdater(expr, assumptions) # for convenience while updating our equation
    expr = eq.update(expr.association(initIdx, initIdx+length, assumptions=assumptions)) # modified 1/13/2020 by wdc
    # expr = eq.update(expr.association(initIdx, length, assumptions=assumptions))
    expr = eq.update(expr.commutation(initIdx, finalIdx, assumptions=assumptions))
    if disassociate:
        expr = eq.update(expr.disassociation(finalIdx, assumptions=assumptions))
    return eq.relation

def groupCommute(expr, initIdx, finalIdx, length, disassociate=True, assumptions=USE_DEFAULTS):
    '''
    Derive a commuted form of the given expr expression on a group of multiple
    operands by associating them together first.
    If 'dissassociate' is true, the group will be disassociated at end.
    '''
    if initIdx < 0: initIdx = len(expr.operands)+initIdx # use wrap-around indexing
    if finalIdx < 0: finalIdx = len(expr.operands)+finalIdx # use wrap-around indexing
    if length==1:
        return expr.commute(initIdx, finalIdx, assumptions=assumptions)

    expr = expr.associate(initIdx, length, assumptions=assumptions)
    expr = expr.commute(initIdx, finalIdx, assumptions=assumptions)
    if disassociate:
        expr = expr.disassociate(finalIdx, assumptions=assumptions)
    return expr

def pairwiseEvaluation(expr, assumptions):
    '''
    Evaluation routine applicable to associative operations in which
    operands at the beginning are paired and evaluated sequentially.
    '''
    from proveit import TransRelUpdater
    # successively evaluate and replace the operation performed on
    # the first two operands

    eq = TransRelUpdater(expr, assumptions) # for convenience while updating our equation

    if len(expr.operands)==2:
        raise ValueError("pairwiseEvaluation may only be used when there are more than 2 operands")
    while len(expr.operands) > 2:
        expr = eq.update(expr.association(0, length=2, assumptions=assumptions))
        expr = eq.update(expr.innerExpr().operands[0].evaluation(assumptions))
    eq.update(expr.evaluation(assumptions=assumptions))
    return eq.relation

def generic_permutation(expr, new_order=None, cycles=None,
                        assumptions=USE_DEFAULTS):
    '''
    '''
    # check validity of default param usage: should have new_order list
    # OR list of cycles, but not both
    if new_order is None and cycles is None:
        raise ValueError("Need to specify either a new ordering in "
                         "the form of new_order = list OR "
                         "cycles = list of tuples.")
    if not new_order is None and not cycles is None:
        raise ValueError("Need to specify EITHER new_order OR cycles, "
                         "but not both.")

    # check validity of provided index values: 
    # (1) each index i needs to be 0 ≤ i ≤ n-1;
    # (2) set of indices provided in new_order needs to be complete,
    #     i.e. consisting of ints 0, 1, 2, …, n-1 (but we allow cycle
    #     notation to omit length-1 cycles)
    # (3) cannot have repeated indices
    expected_number_of_indices = len(expr.operands)
    expected_indices_set = set(range(0, expected_number_of_indices))
    # might be able to condense some of new_order and cycles together
    # later, but somewhat challenging if we allow cycles to omit
    # length-1 cycles
    if new_order:
        given_indices_list = new_order
        given_indices_set = set(new_order)
        if len(given_indices_list) > expected_number_of_indices:
            raise ValueError("new_order specification contains too "
                             "many items, listing {2} indices when "
                             "it should list {0} indices from 0 to {1}".
                             format(expected_number_of_indices,
                                    expected_number_of_indices - 1,
                                    len(new_order)))
        unexpected_indices_set = given_indices_set - expected_indices_set
        if len(unexpected_indices_set) != 0:
            raise IndexError("Index or indices out of bounds: {0}. "
                             "new_order should be a list of indices "
                             "i such that 0 ≤ i ≤ {1}.".
                             format(unexpected_indices_set,
                                    expected_number_of_indices - 1))
        missing_indices_set = expected_indices_set - given_indices_set
        if len(missing_indices_set) != 0:
            raise ValueError("new_order specification is missing "
                             "indices: {}.".format(missing_indices_set))

    if cycles:
        # collect the indices from the cycles
        given_indices_list = []
        for cycle in cycles:
            for i in cycle:
                given_indices_list.append(i)
        given_indices_set = set(given_indices_list)
        if len(given_indices_list) > expected_number_of_indices:
            raise ValueError("cycles specification contains too "
                             "many items, providing {0} indices when "
                             "it should provide no more than {1} "
                             "indices with values from 0 to {2}".
                             format(len(given_indices_list),
                                    expected_number_of_indices,
                                    expected_number_of_indices - 1))
        unexpected_indices_set = given_indices_set - expected_indices_set
        if len(unexpected_indices_set) != 0:
            raise IndexError("Index or indices out of bounds: {0}. "
                             "cycles should only contain indices "
                             "i such that 0 ≤ i ≤ {1}.".
                             format(unexpected_indices_set,
                                    expected_number_of_indices - 1))
        # For cycles, we allow user to omit length-1 cycles
        # so we do NOT need to check for missing indices.
        # Instead, once cycles have passed all the tests,
        # convert to new_order list
        new_order = list(range(0, expected_number_of_indices))
        for cycle in cycles:
            tempCycleLength = len(cycle)
            for i in range(0, tempCycleLength):
                new_order[cycle[i]] = cycle[(i + 1)%tempCycleLength]
        # quick check for duplicates in new_order (can't check it 
        # earlier because there might be legitimate duplicates during
        # the cycles-to-new_order construction process):
        if len(new_order) != len(set(new_order)):
            raise IndexError("Index or indices duplicated in cycles "
                             "specification. cycles should contain "
                             "only a single instance of any specific "
                             "index value.")


    # if user-supplied args check out, then we can continue,
    # regardless of whether user has supplied new_order or cycles
    from proveit import TransRelUpdater

    current_order = list(range(0, expected_number_of_indices))
    desired_order = new_order # notice this isn't a deep copy

    # No need to explicitly check for a trivial (non)-permutation;
    # the eq.relation will hold this for us

    # for convenience while updating our equation
    eq = TransRelUpdater(expr, assumptions)

    while current_order != desired_order:

        # find 1st location where the lists differ and the desired
        # index value there, using set comprehension
        temp_order_diff_info = next(
                (idx, x, y) for idx, (x, y) in enumerate(
                zip(current_order, desired_order)) if x != y)
        initIdx = current_order.index(temp_order_diff_info[2])
        finalIdx = temp_order_diff_info[0]
        expr = eq.update(expr.permutationSimple(
                initIdx, finalIdx, assumptions=assumptions))
        # update current_order to reflect step-wise change
        current_order.remove(temp_order_diff_info[2])
        current_order.insert(finalIdx, temp_order_diff_info[2])

    return eq.relation

