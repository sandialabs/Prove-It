from proveit import USE_DEFAULTS, single_or_composite_expression


def apply_commutation_thm(expr, init_idx, final_idx, binary_thm, leftward_thm,
                          rightward_thm, assumptions=USE_DEFAULTS):

    from proveit.logic import Equals, Set, SetEquiv
    from proveit.numbers import num

    # check validity of default usage of indices
    if init_idx is None or final_idx is None:
        if len(expr.operands) != 2:
            raise IndexError("You may use default 'init_idx' or "
                             "'final_idx' values when applying "
                             "commutation only if your set or "
                             "set-like object contains exactly 2 "
                             "elements.")
        if init_idx is not final_idx:
            raise IndexError("When applying commutation, you must "
                             "either supply both 'init_idx' and "
                             "'final_idx' or supply neither (allowed "
                             "when there are only 2 elements)")
        init_idx, final_idx = 0, 1  # defaults when there are 2 operands

    # transform any wrap-around indexing for simplicity
    # this needs work actually …
    if init_idx < 0:
        init_idx = len(expr.operands) + init_idx
    if final_idx < 0:
        final_idx = len(expr.operands) + final_idx

    # check validity of supplied index values
    if init_idx >= len(expr.operands):
        raise IndexError("'init_idx' = {0} is out of range. Should "
                         "have 0 ≤ init_idx ≤ {1}.".
                         format(init_idx, len(expr.operands) - 1))
    if final_idx >= len(expr.operands):
        raise IndexError("'final_idx' = {0} is out of range. Should "
                         "have 0 ≤ final_idx ≤ {1}.".
                         format(final_idx, len(expr.operands) - 1))

    # trivial commutation (i.e. non-commutation)
    if init_idx == final_idx:
        return Equals(expr, expr).prove()

    # number of operands or elements = 2
    if len(expr.operands) == 2 and set([init_idx, final_idx]) == {0, 1}:
        A, B = binary_thm.all_instance_vars()
        return binary_thm.instantiate(
            {A: expr.operands[0], B: expr.operands[1]}, assumptions=assumptions)

    # number of operands is ≥ 3
    if init_idx < final_idx:
        thm = rightward_thm
        l, m, n, A, B, C, D = thm.all_instance_vars()
        Asub, Bsub, Csub, Dsub = (
            expr.operands[:init_idx], expr.operands[init_idx],
            expr.operands[init_idx + 1:final_idx + 1], expr.operands[final_idx + 1:])
        l_sub, m_sub, n_sub = num(len(Asub)), num(len(Csub)), num(len(Dsub))
    else:
        thm = leftward_thm
        l, m, n, A, B, C, D = thm.all_instance_vars()
        Asub, Bsub, Csub, Dsub = (
            expr.operands[:final_idx], expr.operands[final_idx:init_idx],
            expr.operands[init_idx], expr.operands[init_idx + 1:])
        l_sub, m_sub, n_sub = num(len(Asub)), num(len(Bsub)), num(len(Dsub))
    return thm.instantiate(
        {l: l_sub, m: m_sub, n: n_sub, A: Asub, B: Bsub, C: Csub, D: Dsub},
        assumptions=assumptions)


def apply_association_thm(
        expr,
        start_idx,
        length,
        thm,
        assumptions=USE_DEFAULTS):
    from proveit import ExprTuple
    from proveit.logic import Equals
    beg = start_idx
    if beg < 0:
        beg = len(expr.operands) + beg  # use wrap-around indexing
    end = beg + length
    if end > len(expr.operands):
        raise IndexError("'start_idx+length' out of bounds: %d > %d." % (
                         end, len(expr.operands)))
    if beg == 0 and end == len(expr.operands):
        # association over the entire range is trivial:
        return Equals(expr, expr).prove()  # simply the self equality
    i, j, k, A, B, C = thm.all_instance_vars()
    _A = ExprTuple(*expr.operands[:beg])
    _B = ExprTuple(*expr.operands[beg:end])
    _C = ExprTuple(*expr.operands[end:])
    _i = _A.length(assumptions)
    _j = _B.length(assumptions)
    _k = _C.length(assumptions)
    return thm.instantiate({i: _i, j: _j, k: _k, A: _A, B: _B, C: _C},
                           assumptions=assumptions)


def apply_disassociation_thm(expr, idx, thm=None, assumptions=USE_DEFAULTS):
    from proveit import ExprTuple
    if idx < 0:
        idx = len(expr.operands) + idx  # use wrap-around indexing
    if idx >= len(expr.operands):
        raise IndexError("'idx' out of range for disassociation")
    if not isinstance(expr.operands[idx], expr.__class__):
        raise ValueError(
            "Expecting %d index of %s to be grouped (i.e., a nested expression of the same type)" %
            (idx, str(expr)))
    i, j, k, A, B, C = thm.all_instance_vars()
    _A = ExprTuple(*expr.operands[:idx])
    _B = expr.operands[idx].operands
    _C = ExprTuple(*expr.operands[idx + 1:])
    _i = _A.length(assumptions)
    _j = _B.length(assumptions)
    _k = _C.length(assumptions)
    return thm.instantiate({i: _i, j: _j, k: _k, A: _A, B: _B, C: _C},
                           assumptions=assumptions)


def group_commutation(
        expr,
        init_idx,
        final_idx,
        length,
        disassociate=True,
        assumptions=USE_DEFAULTS):
    '''
    Derive a commutation equivalence on a group of multiple operands by
    associating them together first.  If 'dissassociate' is true, the
    group will be disassociated at end. For example, the following call:
    Or(A,B,C,D).group_commutation(0, 1, length=2,
                                 assumptions=in_bool(A,B,C,D))
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

    # use the following to allow/acknowledge wrap-around indexing
    if init_idx < 0:
        init_idx = len(expr.operands) + init_idx     # wrap
    if final_idx < 0:
        final_idx = len(expr.operands) + final_idx  # wrap
    if length == 1:
        return expr.commutation(init_idx, final_idx, assumptions=assumptions)

    # for convenience while updating our equation:
    eq = TransRelUpdater(expr, assumptions)
    expr = eq.update(
        expr.association(
            init_idx,
            length,
            assumptions=assumptions))
    expr = eq.update(expr.commutation(init_idx, final_idx,
                                      assumptions=assumptions))
    if disassociate:
        expr = eq.update(
            expr.disassociation(
                final_idx,
                assumptions=assumptions))
    return eq.relation


def group_commute(expr, init_idx, final_idx, length, disassociate=True,
                  assumptions=USE_DEFAULTS):
    '''
    Derive a commuted form of the given expr expression on a group of
    multiple operands by associating them together first.
    If 'dissassociate' is true, the group will be disassociated at end.
    '''
    # use the following to allow/acknowledge wrap-around indexing
    if init_idx < 0:
        init_idx = len(expr.operands) + init_idx     # wrap
    if final_idx < 0:
        final_idx = len(expr.operands) + final_idx  # wrap
    if length == 1:
        return expr.commute(init_idx, final_idx, assumptions=assumptions)

    expr = expr.associate(init_idx, length, assumptions=assumptions)
    expr = expr.commute(init_idx, final_idx, assumptions=assumptions)
    if disassociate:
        expr = expr.disassociate(final_idx, assumptions=assumptions)
    return expr


def pairwise_evaluation(expr, assumptions):
    '''
    Evaluation routine applicable to associative operations in which
    operands at the beginning are paired and evaluated sequentially.
    '''
    from proveit import TransRelUpdater
    # successively evaluate and replace the operation performed on
    # the first two operands

    # for convenience while updating our equation:
    eq = TransRelUpdater(expr, assumptions)

    if len(expr.operands) == 2:
        raise ValueError("pairwise_evaluation may only be used when there "
                         "are more than 2 operands.")
    while len(expr.operands) > 2:
        expr = eq.update(
            expr.association(
                0,
                length=2,
                assumptions=assumptions))
        expr = eq.update(expr.inner_expr().operands[0].evaluation(assumptions))
    eq.update(expr.evaluation(assumptions=assumptions))
    return eq.relation


def generic_permutation(expr, new_order=None, cycles=None,
                        assumptions=USE_DEFAULTS):
    '''
    Deduce that the expression expr is equal to a new_expr which is
    the same class and in which the operands at indices 0, 1, …, n-1
    have been reordered as specified EITHER by the new_order list OR
    by the cycles list parameter. For example, if expr were the
    enumerated Set S = {a, b, c, d}, then:
        generic_permutation(S, new_order=[0, 2, 3, 1]) and
        generic_permutation(S, cycles=[(1, 2, 3)]) would both
    return |- {a, b, c, d} = {a, c, d, b}.
    This generic_permutation method can work with any expression type
    which enjoys commutativity of its operands and has established
    the corresponding permutation_move() method and related axioms or
    theorems.
    '''
    # check validity of default param usage: should have new_order list
    # OR list of cycles, but not both
    if new_order is None and cycles is None:
        raise ValueError("Need to specify either a new ordering in "
                         "the form of new_order = list OR "
                         "cycles = list of tuples.")
    if new_order is not None and cycles is not None:
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
            temp_cycle_length = len(cycle)
            for i in range(0, temp_cycle_length):
                new_order[cycle[i]] = cycle[(i + 1) % temp_cycle_length]
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
    desired_order = new_order  # notice this isn't a deep copy

    # No need to explicitly check for a trivial (non)-permutation;
    # the eq.relation will hold this for us

    # for convenience while updating our equation
    eq = TransRelUpdater(expr, assumptions)

    while current_order != desired_order:

        # Use set comprehension to find 1st index where the
        # current_order and desired_order lists differ and determine
        # the desired_order value at that location
        temp_order_diff_info = next(
            (idx, x, y) for idx, (x, y) in enumerate(
                zip(current_order, desired_order)) if x != y)
        # extract the init and final indices for the permutation
        init_idx = current_order.index(temp_order_diff_info[2])
        final_idx = temp_order_diff_info[0]
        expr = eq.update(expr.permutation_move(
            init_idx, final_idx, assumptions=assumptions))
        # update current_order to reflect step-wise change
        current_order.remove(temp_order_diff_info[2])
        current_order.insert(final_idx, temp_order_diff_info[2])

    return eq.relation
