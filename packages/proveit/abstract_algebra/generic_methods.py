from proveit import (defaults, USE_DEFAULTS, single_or_composite_expression,
                     prover, equality_prover)

@prover
def apply_commutation_thm(expr, init_idx, final_idx, binary_thm, leftward_thm,
                          rightward_thm, **defaults_config):

    from proveit.logic import Equals, Set, SetEquiv
    from proveit.numbers import num

    # check validity of default usage of indices
    if init_idx is None or final_idx is None:
        if expr.operands.num_entries() != 2:
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
        init_idx = expr.operands.num_entries() + init_idx
    if final_idx < 0:
        final_idx = expr.operands.num_entries() + final_idx

    # check validity of supplied index values
    if init_idx >= expr.operands.num_entries():
        raise IndexError("'init_idx' = {0} is out of range. Should "
                         "have 0 ≤ init_idx ≤ {1}.".
                         format(init_idx, expr.operands.num_entries() - 1))
    if final_idx >= expr.operands.num_entries():
        raise IndexError("'final_idx' = {0} is out of range. Should "
                         "have 0 ≤ final_idx ≤ {1}.".
                         format(final_idx, expr.operands.num_entries() - 1))

    # trivial commutation (i.e. non-commutation)
    if init_idx == final_idx:
        return Equals(expr, expr).prove()

    # number of operands or elements = 2
    if expr.operands.num_entries() == 2 and set([init_idx, final_idx]) == {0, 1}:
        A, B = binary_thm.all_instance_vars()
        return binary_thm.instantiate(
            {A: expr.operands[0], B: expr.operands[1]})

    # number of operands is ≥ 3
    if init_idx < final_idx:
        thm = rightward_thm
        l, m, n, A, B, C, D = thm.all_instance_vars()
        _A, _B, _C, _D = (
            expr.operands[:init_idx], expr.operands[init_idx],
            expr.operands[init_idx + 1:final_idx + 1], expr.operands[final_idx + 1:])
        _l = _A.num_elements()
        _m = _C.num_elements()
        _n = _D.num_elements()
    else:
        thm = leftward_thm
        l, m, n, A, B, C, D = thm.all_instance_vars()
        _A, _B, _C, _D = (
            expr.operands[:final_idx], expr.operands[final_idx:init_idx],
            expr.operands[init_idx], expr.operands[init_idx + 1:])
        _l = _A.num_elements()
        _m = _B.num_elements()
        _n = _D.num_elements()
    return thm.instantiate(
        {l: _l, m: _m, n: _n, A: _A, B: _B, C: _C, D: _D})

@prover
def apply_association_thm(expr, start_idx, length, thm, **defaults_config):
    from proveit.logic import Equals
    beg = start_idx
    if beg < 0:
        beg = expr.operands.num_entries() + beg  # use wrap-around indexing
    end = beg + length
    if end > expr.operands.num_entries():
        raise IndexError("'start_idx+length' out of bounds: %d > %d." % (
                         end, expr.operands.num_entries()))
    if beg == 0 and end == expr.operands.num_entries():
        # association over the entire range is trivial:
        return Equals(expr, expr).prove()  # simply the self equality
    i, j, k, A, B, C = thm.all_instance_vars()
    _A = expr.operands[:beg]
    _B = expr.operands[beg:end]
    _C = expr.operands[end:]
    _i = _A.num_elements()
    _j = _B.num_elements()
    _k = _C.num_elements()
    with expr.__class__.temporary_simplification_directives() as \
            tmp_directives:
        tmp_directives.ungroup = False
        return thm.instantiate({i: _i, j: _j, k: _k, A: _A, B: _B, C: _C})

@prover
def apply_disassociation_thm(expr, idx, thm=None, **defaults_config):
    if idx < 0:
        idx = expr.operands.num_entries() + idx  # use wrap-around indexing
    if idx >= expr.operands.num_entries():
        raise IndexError("'idx' out of range for disassociation")
    if not isinstance(expr.operands[idx], expr.__class__):
        raise ValueError(
            "Expecting %d index of %s to be grouped (i.e., a nested expression of the same type)" %
            (idx, str(expr)))
    i, j, k, A, B, C = thm.all_instance_vars()
    _A = expr.operands[:idx]
    _B = expr.operands[idx].operands
    _C = expr.operands[idx + 1:]
    _i = _A.num_elements()
    _j = _B.num_elements()
    _k = _C.num_elements()
    return thm.instantiate({i: _i, j: _j, k: _k, A: _A, B: _B, C: _C})


@prover
def group_commutation(expr, init_idx, final_idx, length, disassociate=True,
                      **defaults_config):
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
        init_idx = expr.operands.num_entries() + init_idx     # wrap
    if final_idx < 0:
        final_idx = expr.operands.num_entries() + final_idx  # wrap
    if length == 1:
        return expr.commutation(init_idx, final_idx)

    # for convenience while updating our equation:
    eq = TransRelUpdater(expr)
    expr = eq.update(
        expr.association(init_idx, length, preserve_all=True))
    expr = eq.update(expr.commutation(
            init_idx, final_idx, 
            preserve_all = defaults.preserve_all or disassociate))
    if disassociate:
        expr = eq.update(
            expr.disassociation(final_idx))
    return eq.relation

@prover
def group_commute(expr, init_idx, final_idx, length, disassociate=True,
                  **defaults_config):
    '''
    Derive a commuted form of the given expr expression on a group of
    multiple operands by associating them together first.
    If 'dissassociate' is true, the group will be disassociated at end.
    '''
    # use the following to allow/acknowledge wrap-around indexing
    if init_idx < 0:
        init_idx = expr.operands.num_entries() + init_idx     # wrap
    if final_idx < 0:
        final_idx = expr.operands.num_entries() + final_idx  # wrap
    if length == 1:
        return expr.commute(init_idx, final_idx)

    expr = expr.associate(init_idx, length, preserve_all=True)
    expr = expr.commute(init_idx, final_idx,
                        preserve_all = defaults.preserve_all or disassociate)
    if disassociate:
        expr = expr.disassociate(final_idx)
    return expr

@prover
def pairwise_evaluation(expr, **defaults_config):
    '''
    Evaluation routine applicable to associative operations in which
    operands at the beginning are paired and evaluated sequentially.
    '''
    from proveit import TransRelUpdater
    from proveit.logic import is_irreducible_value
    # successively evaluate and replace the operation performed on
    # the first two operands

    # for convenience while updating our equation:
    eq = TransRelUpdater(expr)

    if is_irreducible_value(expr):
        # The expression is already irreducible, so we are done.
        return eq.relation

    if expr.operands.num_entries() == 2:
        raise ValueError("pairwise_evaluation may only be used when there "
                         "are more than 2 operands.")

    # While there are more than 2 operands, associate the first 2
    # and auto-simplify.
    while expr.operands.num_entries() > 2:
        expr = eq.update(expr.association(0, length=2, auto_simplify=True))
        if is_irreducible_value(expr):
            # The new expression is irreducible, so we are done.
            return eq.relation
        elif not is_irreducible_value(expr.operands[0]):
            # Auto-simplication failed to convert the first operand
            # to an irreducible value, so break out of this loop
            # and generate an appropriate error by trying to
            # evaluate it directly.
            expr = eq.update(expr.inner_expr().operands[0].evaluate())
    return eq.relation

@equality_prover('generic_permuted', 'generic_permute')
def generic_permutation(expr, new_order=None, cycles=None, **defaults_config):
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
    expected_number_of_indices = expr.operands.num_entries()
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
    eq = TransRelUpdater(expr)

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
        expr = eq.update(expr.permutation_move(init_idx, final_idx, auto_simplify=False))
        # update current_order to reflect step-wise change
        current_order.remove(temp_order_diff_info[2])
        current_order.insert(final_idx, temp_order_diff_info[2])

    return eq.relation
