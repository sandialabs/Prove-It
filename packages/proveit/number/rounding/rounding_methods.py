from proveit import defaults, TransRelUpdater, USE_DEFAULTS

def apply_roundingElimination(expr, roundingEliminationThm,
                              assumptions=USE_DEFAULTS):
    '''
    Let F(x) represent the relevant Ceil(x), Floor(x), or Round(x)
    fxn calling the apply_roundingElimination() method from the
    respective F(x).roundingElimination() method.
    For the trivial case of F(x) where the operand x is already
    an integer, derive and return this rounding F expression equated
    with the operand itself: |- F(x) = x. For example, |- Ceil(x) = x.
    Assumptions may be necessary to deduce necessary conditions
    (for example, that x actually is an integer) for the simplification.
    This method is utilized by the F(x).apply_reducedSimplification()
    method, indirectly via the F(x).roundingElimination() method, but
    only after the operand x is verified to already be proven (or
    assumed) to be an integer.
    For the case where the operand is of the form x = real + int,
    see the apply_roundingExtraction() function.
    '''
    from proveit._common_ import x

    # among other things, convert any assumptions=None
    # to assumptions=() to avoid later len() errors
    assumptions = defaults.checkedAssumptions(assumptions)

    return roundingEliminationThm.instantiate(
                {x:expr.operand}, assumptions=assumptions)

def apply_roundingExtraction(expr, roundingExtractionThm, idx_to_extract=None,
                             assumptions=USE_DEFAULTS):
    '''
    Let F(x) represent the relevant Ceil(x), Floor(x), or Round(x)
    fxn calling the apply_roundingExtraction() method from the
    respective F(x).roundingExtraction() method. For the case of F(x)
    where the operand x = x_real + x_int, derive and return
    F(x) = F(x_real) + x_int (thus 'extracting' the integer component
    of x out from inside the function F()). The idx_to_extract is the
    zero-based index of the item in the operands of an Add(a, b, …, n)
    expression to attempt to extract. Assumptions may be necessary to
    deduce necessary conditions (for example, that x_int actually is
    an integer) for the simplification. For example,
    let F(x) = Ceil(x+2+y). Calling
        F(x).roundingExtraction(
                1, assumptions=[InSet(x, Reals), InSet(y, Reals)]),
    will eventually end up here and return
        |- F(x) = Ceil(x+y) + 2
    This method is utilized by the F(x).apply_reducedSimplification()
    method, indirectly via the F(x).roundingExtraction() method, but
    only after the operand x is verified to already be proven (or
    assumed) to be the sum of reals and integers.
    For the case where the entire operand x is itself an integer,
    see the roundingElimination() method.
    This works only if the operand x is an instance of the Add
    class at its outermost level, e.g. x = Add(a, b, …, n). The
    operands of that Add class can be other things, but the extraction
    will work only if the inner operands a, b, ..., n are simple.
    '''
    from proveit._common_ import n, x, y
    from proveit.number import Add
    # from ._theorems_ import roundOfRealPlusInt

    # among other things, convert any assumptions=None
    # to assumptions=() to avoid later len() errors
    assumptions = defaults.checkedAssumptions(assumptions)

    # for convenience while updating our equation
    eq = TransRelUpdater(expr, assumptions)

    # first use Add.commutation to (re-)arrange operands to comform
    # to theorem format, using user-supplied idx_to_extract
    if isinstance(expr.operand, Add):
        expr = eq.update(expr.innerExpr().operand.commutation(idx_to_extract,
                len(expr.operand.operands)-1, assumptions=assumptions))

        # An association step -- because the later application of
        # the roundOfRealPlusInt thm produces a grouping of the 
        # Round operands in the chain of equivalences.
        # BUT, only perform the association if multiple operands are
        # needing to be associated:
        if len(expr.operand.operands)-1 > 1:
            expr = eq.update(expr.innerExpr().operand.association(
                    0, len(expr.operand.operands)-1, assumptions=assumptions))


        # then update by applying the roundOfRealPlusInt thm
        x_sub = expr.operand.operands[0]
        n_sub = expr.operand.operands[1]
        expr = eq.update(roundingExtractionThm.instantiate(
                {x:x_sub, n:n_sub}, assumptions=assumptions))

        return eq.relation
    else:
        raise ValueError("In attempting f(x).apply_roundingExtraction(), "
                         "the operand x is not of class 'Add'.")

def apply_reducedSimplification(expr, assumptions=USE_DEFAULTS):
    '''
    Let F(x) represent the relevant Ceil(x), Floor(x), or Round(x)
    fxn calling the apply_reducedSimplification() method from the
    respective F(x).doReducedSimplification() method (which itself is
    likely called from the F(x).simplification() method).
    For the trivial case F(x) where the operand x is already
    known to be or assumed to be an integer, derive and return this
    F(x) expression equated with the operand itself: F(x) = x. For
    example, |- Round(2) = 2 or |- Floor(1) = 1. Assumptions may be
    necessary to deduce necessary conditions for the simplification
    (for example, for deducing that the operand really is an integer).
    For the case where the operand is of the form x = real + int,
    derive and return this F(x) expression equated with F(real) + int.
    For example, |- Floor(x + 2) = Floor(x) + 2. Again, assumptions
    may be necessary to deduce the appropriate set containments for
    the operands within the Add operand x.
    '''
    from proveit._common_ import n, x
    from proveit.logic import InSet
    from proveit.number import Add, Integer, Reals

    # among other things, convert any assumptions=None
    # to assumptions=() (thus averting len(None) errors)
    assumptions = defaults.checkedAssumptions(assumptions)

    #-- -------------------------------------------------------- --#
    #-- Case (1): F(x) where entire operand x is known or        --#
    #--           assumed to be an Integer.                      --#
    #-- -------------------------------------------------------- --#
    if InSet(expr.operand, Integer).proven(assumptions=assumptions):
        # Entire operand is known to be or assumed to be an integer
        # so we can simply remove the Ceil, Floor, or Round wrapper
        return expr.roundingElimination(assumptions)

    #-- -------------------------------------------------------- --#
    #-- Case (2): F(x) where entire operand x is not yet known   --*
    #--           to be an Integer but can EASILY be proven      --#
    #--           to be an Integer.                              --#
    #-- -------------------------------------------------------- --#
    if expr.operand in InSet.knownMemberships.keys():
        from proveit.logic.set_theory import ProperSubset, SubsetEq
        for kt in InSet.knownMemberships[expr.operand]:
            if kt.isSufficient(assumptions):
                if (SubsetEq(kt.expr.operands[1], Integer).proven(assumptions)
                    or 
                    ProperSubset(kt.expr.operands[1], Integer).proven(assumptions)):
                    InSet(expr.operand, Integer).prove()
                    return expr.roundingElimination(assumptions)


    # for updating our equivalence claim(s) for the
    # remaining possibilities
    eq = TransRelUpdater(expr, assumptions)

    #-- -------------------------------------------------------- --#
    #-- Case (3): F(x) = F(Add(a,b,...,n)), where operand x is   --#
    #--           an Add object, not known or assumed to be an   --#
    #--           an int, but addends might be real and integer  --#
    #--           numbers.                                       --#
    #-- -------------------------------------------------------- --#
    if isinstance(expr.operand, Add):
        # Try to partition all suboperands into Integer vs.
        # Non-Integer, and if there is at least one integer, try to
        # apply the extraction theorem (allowing an error message
        # if the instantiation fails).

        subops = expr.operand.operands

        # Collect indices of operands known or assumed to be
        # integers versus real numbers versus neither
        indices_of_known_ints = []
        indices_of_non_ints = []
        for i in range(len(subops)):
            the_subop = subops[i]

            # (a) first perform easiest check: is the subop already known
            #     to be an Integer?
            if InSet(the_subop, Integer).proven(assumptions):
                indices_of_known_ints.append(i)

            # (b) then try something just a little harder
            elif the_subop in InSet.knownMemberships.keys():
                from proveit.logic.set_theory import ProperSubset, SubsetEq
                for kt in InSet.knownMemberships[the_subop]:
                    if kt.isSufficient(assumptions):
                        if (SubsetEq(kt.expr.operands[1], Integer).
                                proven(assumptions) or
                            ProperSubset(kt.expr.operands[1], Integer).
                                proven(assumptions)):
                            InSet(the_subop, Integer).prove()
                            indices_of_known_ints.append(i)
                            break

            # (c) then if the_subop is not an integer, note that instead
            if (i not in indices_of_known_ints):
                # we categorize it as a non-integer
                indices_of_non_ints.append(i)

        if len(indices_of_known_ints)>0:
            # Then we have at least one known integer addend, so we
            # rearrange and group the addends, associating the non-ints
            # and associating the ints
            original_addends = list(subops)
            desired_order_by_index = list(
                    indices_of_non_ints + indices_of_known_ints)
            # commute to put reals first, followed by ints
            for i in range(len(original_addends)):
                init_idx = expr.operand.operands.index(
                        original_addends[desired_order_by_index[i]])
                expr = eq.update(
                        expr.innerExpr().operand.commutation(
                                init_idx, i, assumptions=assumptions))

            # associate the non-integers (if more than 1)
            if len(indices_of_non_ints) > 1:
                # associate those elements (already re-arranged to
                # be at the front of the operand.operands):
                expr = eq.update(
                        expr.innerExpr().operand.association(
                                0, len(indices_of_non_ints),
                                assumptions=assumptions))

            # associate the known integers (if more than 1)
            if len(indices_of_known_ints) > 1:
                # associate those elements (already re-arranged to
                # be at the end of the operand.operands):
                if len(indices_of_non_ints) > 0:
                    start_idx = 1
                else:
                    start_idx = 0
                expr = eq.update(
                        expr.innerExpr().operand.association(
                                start_idx,
                                len(indices_of_known_ints),
                                assumptions=assumptions))

            if len(indices_of_known_ints)==len(subops):
                # all the addends were actually integers
                # could probably short-circuit this earlier!
                expr = eq.update(expr.roundingElimination(assumptions))
            else:
                expr = eq.update(expr.roundingExtraction(1, assumptions))
            return eq.relation

        else:
            # We did not find any integers.
            # Instead of returning an error, simply return the original
            # rounding expression equal to itself
            return eq.relation

    #-- -------------------------------------------------------- --#
    #-- Case (4): F(x) where operand x is not known or assumed   --#
    #--           to be an Integer and x is not an Add object    --#
    #-- -------------------------------------------------------- --#
    # apply_reducedSimplification() function is expecting simpler
    # operands; instead of returning an error, though, simply return
    # the trivial equivalence of the original expression with itself
    return eq.relation
        

def rounding_deduceInNumberSet(expr, number_set, roundingRealClosureThm,
                               roundingRealPosClosureThm,
                               assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        Ceil, Floor, or Round expression is in that number set using
        the appropriate closure theorem.
        '''
        from proveit import ProofFailure
        from proveit._common_ import x
        from proveit.logic import InSet
        from proveit.number import Integer, Natural

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Integer:
            return roundingRealClosureThm.instantiate(
                        {x:expr.operand}, assumptions=assumptions)

        if number_set == Natural:
            return roundingRealPosClosureThm.instantiate(
                        {x:expr.operand}, assumptions=assumptions)

        msg = ("The rounding_methods.py function "
               "'rounding_deduceInNumberSet()' is not implemented for the "
               "%s set"%str(number_set))
        raise ProofFailure(InSet(expr, number_set), assumptions, msg)

