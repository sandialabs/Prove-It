from proveit import (Judgment, UnsatisfiedPrerequisites,
                     defaults, USE_DEFAULTS, 
                     single_or_composite_expression,
                     prover, equality_prover)

@prover
def apply_commutation_thm(expr, init_idx, final_idx, binary_thm, leftward_thm,
                          rightward_thm,  *, repl_map_extras=None,
                          **defaults_config):

    from proveit.logic import Equals, Set, SetEquiv
    from proveit.numbers import num
    if repl_map_extras is None:
        repl_map_extras = dict()
    
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
        A, B = [_v for _v in binary_thm.all_instance_vars() if 
                _v not in repl_map_extras]
        return binary_thm.instantiate(
            {A: expr.operands[0], B: expr.operands[1]})

    # number of operands is ≥ 3
    if init_idx < final_idx:
        thm = rightward_thm
        _A, _B, _C, _D = (
            expr.operands[:init_idx], expr.operands[init_idx],
            expr.operands[init_idx + 1:final_idx + 1], expr.operands[final_idx + 1:])
        _l = _A.num_elements()
        _m = _C.num_elements()
        _n = _D.num_elements()
    else:
        thm = leftward_thm
        _A, _B, _C, _D = (
            expr.operands[:final_idx], expr.operands[final_idx:init_idx],
            expr.operands[init_idx], expr.operands[init_idx + 1:])
        _l = _A.num_elements()
        _m = _B.num_elements()
        _n = _D.num_elements()
    l, m, n, A, B, C, D = [_v for _v in thm.all_instance_vars() if 
                           _v not in repl_map_extras]
    repl_map = {l: _l, m: _m, n: _n, A: _A, B: _B, C: _C, D: _D}
    repl_map.update(repl_map_extras)
    return thm.instantiate(repl_map)

def start_and_end_indices(expr, *, start_index, length):
    beg = start_index
    if beg < 0:
        beg = expr.operands.num_entries() + beg  # use wrap-around indexing
    end = beg + length
    if end > expr.operands.num_entries():
        raise IndexError("'start_idx+length' out of bounds: %d > %d." % (
                         end, expr.operands.num_entries()))
    return beg, end

@prover
def apply_association_thm(expr, start_idx, length, thm, *,
                          repl_map_extras=None,
                          **defaults_config):
    from proveit.logic import Equals
    beg, end = start_and_end_indices(
            expr, start_index=start_idx, length=length)
    if beg == 0 and end == expr.operands.num_entries():
        # association over the entire range is trivial:
        return Equals(expr, expr).prove()  # simply the self equality
    if repl_map_extras is None:
        repl_map_extras = dict()
    i, j, k, A, B, C = [_var for _var in thm.all_instance_vars()
                        if _var not in repl_map_extras]
    _A = expr.operands[:beg]
    _B = expr.operands[beg:end]
    _C = expr.operands[end:]
    _i = _A.num_elements()
    _j = _B.num_elements()
    _k = _C.num_elements()
    with expr.__class__.temporary_simplification_directives() as \
            tmp_directives:
        tmp_directives.ungroup = False
        repl_map = {i: _i, j: _j, k: _k, A: _A, B: _B, C: _C}
        repl_map.update(repl_map_extras)
        return thm.instantiate(repl_map)

def checked_disassociation_index(expr, idx):
    if idx < 0:
        idx = expr.operands.num_entries() + idx  # use wrap-around indexing
    if idx >= expr.operands.num_entries():
        raise IndexError("'idx' out of range for disassociation")
    if not isinstance(expr.operands[idx], expr.__class__):
        raise ValueError(
            "Expecting %d index of %s to be grouped (i.e., a nested "
            "expression of the same type)" %
            (idx, str(expr)))  
    return idx

@prover
def apply_disassociation_thm(expr, idx, thm=None, *,
                             repl_map_extras=None, 
                             **defaults_config):
    idx = checked_disassociation_index(expr, idx)
    if repl_map_extras is None:
        repl_map_extras = dict()
    i, j, k, A, B, C = [var for var in thm.all_instance_vars()
                        if var not in repl_map_extras]
    _A = expr.operands[:idx]
    _B = expr.operands[idx].operands
    _C = expr.operands[idx + 1:]
    _i = _A.num_elements()
    _j = _B.num_elements()
    _k = _C.num_elements()
    repl_map = {i: _i, j: _j, k: _k, A: _A, B: _B, C: _C}
    repl_map.update(repl_map_extras)
    return thm.instantiate(repl_map)


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

def prove_via_grouping_ranges(expr, prover_fn):
    '''
    Groups the ExprRange operands of the expression, calls a prover
    type function on this grouped expression, then
    return the resulting judgment after disassociating.
    '''
    from proveit import Judgment, ExprRange
    from proveit.relation import Relation
    range_indices = [
            _k for _k, operand in enumerate(expr.operands)
            if isinstance(operand, ExprRange)]
    grouped_range_version = expr.__class__(
            *[expr.__class__(operand) if isinstance(operand, ExprRange) 
            else operand for operand in expr.operands])
    judgment = prover_fn(grouped_range_version, preserve_all=True)
    defaults.test_judgment = judgment
    assert isinstance(judgment, Judgment)
    if isinstance(judgment.expr, Relation):
        assert judgment.expr.lhs == grouped_range_version, (
                "Expecting %s to be on the left side of %s"%(
                        grouped_range_version, judgment.expr))
        for range_idx in range_indices:
            judgment = judgment.inner_expr().lhs.disassociate(
                    range_idx, preserve_all=True)
    else:
        assert judgment.expr == grouped_range_version, (
                "Expecting %s to %s"%(judgment.expr, grouped_range_version))
        for range_idx in range_indices:
            judgment = judgment.inner_expr().disassociate(
                    range_idx, preserve_all=True)
    return judgment

@prover
def deduce_equality_via_commutation(equality, *, one_side=None,
                                    **defaults_config):
    '''
    Prove the given equality by permuting the operands assuming
    commutivity and/or substitution of sub-expressions.
    
    If 'one_side' is provided, raise a ValueError of it is not
    an Expression on one side of the equality.
    '''
    from proveit.logic import Equals
    if isinstance(equality, Judgment):
        equality = equality.expr
    if not isinstance(equality, Equals):
        raise TypeError("'equality' must be an Equals expression")
    lhs, rhs = equality.lhs, equality.rhs
    if one_side is not None and one_side not in (lhs, rhs):
        raise ValueError("'equality' expected to have %s on one side: "
                         "%s not in {%s, %s}"%(one_side, lhs, rhs))
    if lhs.canonical_form() != rhs.canonical_form():
        raise UnsatisfiedPrerequisites(
                "'deduce_equality_via_commutation' is not applicable "
                "because %s and %s have different canonical forms"
                %(lhs, rhs))
    if lhs.operands.num_entries() != rhs.operands.num_entries():
        raise ValueError("The number of operands do not match on either "
                         "side of %s; 'deduce_equality_via_commutation', "
                         "therefore, is not applicable."
                         %equality)
    lhs_canonical_to_idx = {operand.canonical_form():_k for _k, operand 
                            in enumerate(lhs.operands.entries)}
    
    # Figure out the new order and prove operand equalities 
    # (left vs right) as needed.
    needs_substitutions = False
    new_order = []
    for rhs_operand in rhs.operands.entries:
        lhs_idx = lhs_canonical_to_idx.pop(rhs_operand.canonical_form())
        new_order.append(lhs_idx)
        lhs_operand = lhs.operands[lhs_idx]
        if rhs_operand != lhs_operand:
            Equals(lhs_operand, rhs_operand).prove()
            needs_substitutions = True
    
    if new_order != list(range(lhs.operands.num_entries())):
        # The order is changed; prove the permutation.
        permutation = generic_permutation(lhs, new_order)
    else:
        # No order change -- maybe just needs operand substitutions.
        permutation = Equals(lhs, lhs).conclude_via_reflexivity()
    if needs_substitutions:
        # Prove the equality via direct substitutions.
        eq_via_sub = Equals(permutation.rhs, rhs)
        eq_via_sub.conclude_via_direct_substitution()
        return permutation.apply_transitivity(eq_via_sub)
    # No substitution is needed, so we should be all set.
    assert permutation.expr == equality
    return permutation

@equality_prover('sorted_operands', 'sort_operands')
def sorting_operands(
        expr, *, order_key_fn, **defaults_config):
    '''
    For commutative and associative operations, this method
    equates an original expression to one that may be partially
    sorted according to the given `order_key`.  Ties retain the
    original order.
    '''
    from proveit.logic import Equals
    # See if we should reorder the terms.
    indices = list(range(expr.operands.num_entries()))
    new_order = sorted(indices,
                       key = lambda idx : order_key_fn(expr.operands[idx]))
    if new_order != indices:
        return generic_permutation(expr, new_order)
    return Equals(expr, expr).conclude_via_reflexivity()


@equality_prover('sorted_and_combined_like_operands', 
                 'sort_and_combine_like_operands')
def sorting_and_combining_like_operands(
        expr, *, order_key_fn, likeness_key_fn,
        preserve_likeness_keys=True,
        **defaults_config):
    '''
    For commutative and associative operations, this method
    equates an original expression to one that may be partially
    sorted and "like" operands are combined.
    
    The `likeness_key` function should transform each operand to an
    expression 'key' that is the same for "like" operands.  The likeness
    key of an ExprRange is the likeness key of its body if this key is 
    independent of the ExprRange parameter; otherwise the likeness key 
    is the ExprRange itself.
    
    The "order_key" is used to sort these likeness keys -- ties
    retain the original order w.r.t. which likeness key came first.
    
    Combining the operands is implemented by grouping them together
    (calling the `association` method) and calling 
    `combining_operands` on each one.
    
    If 'preserve_likeness_keys' is True, the likeness keys will 
    be preserved and not simplified even if auto-simplification is on.
    '''
    from proveit import ExprRange
    from proveit import TransRelUpdater
    from proveit.logic import Equals
    if expr.operands.num_entries() <= 1:
        # Nothing to combine or sort.
        return Equals(expr, expr).conclude_via_reflexivity()
    # Separate the types of operands in a dictionary so we can
    # combine like operand.
    key_to_indices = dict()
    key_order = []
    for _k, operand in enumerate(expr.operands):
        if isinstance(operand, ExprRange):
            # For an ExprRange operand, use the body's likeness key
            # iff it is parameter independent.
            key = likeness_key_fn(operand.body)
            if operand.parameter in key.free_vars():
                # It's not parameter independent -- each instance has
                # a different likeness key, so use the ExprRange itself.
                key = operand
        else:
            key = likeness_key_fn(operand)
        if key in key_to_indices:
            key_to_indices[key].append(_k)
        else:
            key_to_indices[key] = [_k]
            # first come first serve:
            key_order.append(key)
    if len(key_to_indices) > 1:
        eq = TransRelUpdater(expr)
        # Reorder the terms so like terms are adjacent.
        new_order = []
        sorted_keys = sorted(key_order, key=order_key_fn)
        for key in sorted_keys:
            new_order.extend(key_to_indices[key])
        # Perform the permutation.
        expr = eq.update(generic_permutation(expr, new_order,
                                             preserve_all=True))
        # Now group the terms so we can combine them.
        for _m, key in enumerate(sorted_keys):
            preserve_expr = key if preserve_likeness_keys else None
            num_like_operands = len(key_to_indices[key])
            if num_like_operands > 1:                    
                # More than one operand to group and combine.
                grouped_operation = expr.__class__(
                        *expr.operands.entries[_m:_m+num_like_operands])
                combination = (grouped_operation.combining_operands(
                        preserve_expr=preserve_expr))
                expr = eq.update(expr.association(
                    _m, length=len(key_to_indices[key]),
                    replacements=[combination],
                    auto_simplify=False))
            elif num_like_operands==1:
                operand = expr.operands[_m]
                if isinstance(operand, ExprRange) and (
                        key != operand):
                    # A single ExprRange to combine.
                    expr = eq.update(expr.inner_expr().operands[_m].
                                     combining_operands(
                                             preserve_expr=preserve_expr))
        return eq.relation
    # Only one type of operand -- combine them.
    preserve_expr = (iter(key_to_indices.keys()) if preserve_likeness_keys 
                     else None)
    return expr.combining_operands(preserve_expr=preserve_expr)

def common_likeness_key(expr, *, likeness_key_fn):
    '''
    Returns 'likeness_key' which must be in common among the operands
    of the 'expr'.  If the operands don't all of the same likeness
    key, a ValueError exception will be raised.

    The `likeness_key` function should transform each operand to a key
    that is the same for "like" operands.  The likeness key of an
    ExprRange is the likeness key of its body if this key is independent
    of the ExprRange parameter; otherwise the likeness key is the
    ExprRange itself.
    
    Useful when implementating 'combining_operands'.
    
    See sorting_and_combining_like_operands.
    '''
    from proveit import ExprRange
    keys = set()
    for _k, operand in enumerate(expr.operands):
        if isinstance(operand, ExprRange):
            # For an ExprRange operand, use the body's likeness key
            # iff it is parameter independent.
            key = likeness_key_fn(operand.body)
            if operand.parameter in key.free_vars():
                # It's not parameter independent -- each instance has
                # a different likeness key, so use the ExprRange itself.
                key = operand
        else:
            key = likeness_key_fn(operand)
        keys.add(key)
    if len(keys) != 1:
        raise ValueError("The likeness keys of the operands of %s are "
                         "not all the same: %s"%(expr, keys))
    return next(iter(keys))
