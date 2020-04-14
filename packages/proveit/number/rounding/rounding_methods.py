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
    This method is utilized by the F(x).doReducedSimplification()
    method, via the F(x).roundingElimination() method, but only after
    the operand x is verified to already be proven (or assumed) to be
    an integer.
    For the case where the operand is of the form x = real + int,
    see the apply_roundingExtraction() function.
    '''
    from proveit._common_ import x

    # among other things, convert any assumptions=None
    # to assumptions=() to avoid later len() errors
    assumptions = defaults.checkedAssumptions(assumptions)

    return roundingEliminationThm.specialize(
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
    This method is utilized by the F(x).doReducedSimplification()
    method, via the F(x).roundingExtraction() method, but only after
    the operand x is verified to already be proven (or assumed) to be
    the sum of reals and integers.
    For the case where the entire operand x is itself an integer,
    see the roundingElimination() method.
    This works only if the operand x is an instance of the Add
    class at its outermost level, e.g. x = Add(a, b, …, n). The
    operands of that Add class can be other things, but the extraction
    is guaranteed to work only if the inner operands a, b, ..., n are
    simple.
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
        expr = eq.update(roundingExtractionThm.specialize(
                {x:x_sub, n:n_sub}, assumptions=assumptions))

        return eq.relation
    else:
        raise ValueError("In attempting f(x).apply_roundingExtraction(), "
                         "the operand x is not of class 'Add'.")

def apply_reducedSimplification(expr, assumptions=USE_DEFAULTS):
    '''
    Let F(x) represent the relevant Ceil(x), Floor(x), or Round(x)
    fxn calling the apply_reducedSimplification() method from the
    respective F(x).doReducedSimplification() method.
    For the trivial case F(x) where the operand x is already
    known to be or assumed to be an integer, derive and return this
    F(x) expression equated with the operand itself: F(x) = x. For
    example, |- Round(2) = 2 or |- Floor(1) = 1.
    Assumptions may be necessary to deduce necessary conditions for
    the simplification. For the case where the operand is of the
    form x = real + int, derive and return this F(x) expression
    equated with F(real) + int. For example,
    |- Floor(x + 2) = Floor(x) + 2
    '''
    from proveit._common_ import n, x
    from proveit.logic import InSet
    from proveit.number import Add, Integers, Reals

    # among other things, convert any assumptions=None
    # to assumptions=()
    assumptions = defaults.checkedAssumptions(assumptions)

    #-- -------------------------------------------------------- --#
    #-- Case (1): F(x) where entire operand x is known or        --#
    #--           assumed to be an Integer.                      --#
    #-- -------------------------------------------------------- --#
    if InSet(expr.operand, Integers).proven(assumptions=assumptions):
        # Entire operand is known to be or assumed to be an integer
        # so we can simply remove the Ceil, Floor, or Round wrapper
        return expr.roundingElimination(assumptions)
    #-- -------------------------------------------------------- --#
    #-- Case (2): F(x) = F(Add(a,b,...,n)), where operand x is   --#
    #--           an Add object, not known or assumed to be an   --#
    #--           an int, but addends might be reals and ints    --#
    #-- -------------------------------------------------------- --#
    elif isinstance(expr.operand, Add):
        # Try to partition all suboperands into ints vs. reals
        
        # for convenience while updating our equation
        eq = TransRelUpdater(expr, assumptions)

        subops = expr.operand.operands

        # Collect indices of operands known or assumed to be
        # ints versus reals versus neither
        indices_of_known_ints = []
        indices_of_reals_not_ints = []
        indices_of_unknowns = []
        for i in range(len(subops)):
            if InSet(subops[i], Integers).proven(assumptions):
                indices_of_known_ints.append(i)
            elif InSet(subops[i], Reals).proven(assumptions):
                indices_of_reals_not_ints.append(i)
            else:
                indices_of_unknowns.append(i)
        if len(indices_of_unknowns) == 0 and len(indices_of_known_ints)>0:
            # each addend is an int or a real, with at least one
            # int, so we should be able to rearrange and partition
            # the addends as such
            original_addends = list(subops)
            desired_order_by_index = list(
                    indices_of_reals_not_ints+indices_of_known_ints)
            # commute to put reals first, followed by ints
            for i in range(len(original_addends)):
                init_idx = expr.operand.operands.index(
                        original_addends[desired_order_by_index[i]])
                expr = eq.update(
                        expr.innerExpr().operand.commutation(
                                init_idx, i, assumptions=assumptions))

            # associate the reals
            if len(indices_of_reals_not_ints) > 1:
                # associate those elements (already re-arranged to
                # be at the front of the operand.operands):
                expr = eq.update(
                        expr.innerExpr().operand.association(
                                0, len(indices_of_reals_not_ints),
                                assumptions=assumptions))
            # associate the ints
            if len(indices_of_known_ints) > 1:
                # associate those elements (already re-arranged to
                # be at the end of the operand.operands):
                if len(indices_of_reals_not_ints) > 0:
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
            # list_of_unknowns might be non-empty
            # and/OR indices_of_known_ints might be empty
            if len(indices_of_unknowns) > 0:
                list_of_unknowns = [subops[i] for i in indices_of_unknowns]
                msg = ("In attempting f(x).apply_reducedSimplification, "
                       "the operands {} are not assumed or proven to be "
                       "Integers or Reals.".format(list_of_unknowns))
            elif len(indices_of_known_ints) == 0:
                msg = ("In attempting f(x).apply_reducedSimplification, no "
                       "operands were found to be assumed or proven to be "
                       "Integers.".format(list_of_unknowns))
            else:
                msg = ("In attempting f(x).apply_reducedSimplification, "
                       "an unknown error has occurred, probably related "
                       "to being able to partition the addends into reals "
                       "and integers.")
            raise ValueError(msg)

    #-- -------------------------------------------------------- --#
    #-- Case (3): F(x) where operand x is not known or assumed   --#
    #--           to be an Integer and x is not an Add object    --#
    #-- -------------------------------------------------------- --#
    else:
        raise ValueError("The doReducedSimplification() method of the "
                         "rounding function f (Ceil, Floor, or Round) is "
                         "expecting simpler operands. Consider reviewing "
                         "the fOfInteger and fOfRealPlusInt theorems "
                         "in the proveit/number/rounding context.")

def rounding_deduceInNumberSet(expr, number_set, roundingRealClosureThm,
                               roundingRealPosClosureThm,
                               assumptions=USE_DEFAULTS):
        '''
        Given a number set number_set, attempt to prove that the given
        Ceil, Floor, or Round expression is in that number set using
        the appropriate closure theorem.
        '''
        from proveit._common_ import x
        from proveit.logic import InSet
        from proveit.number import Integers, Naturals

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        if number_set == Integers:
            return roundingRealClosureThm.specialize(
                        {x:expr.operand}, assumptions=assumptions)

        if number_set == Naturals:
            return roundingRealPosClosureThm.specialize(
                        {x:expr.operand}, assumptions=assumptions)

        msg = ("The rounding_methods.py function "
               "'rounding_deduceInNumberSet()' is not implemented for the "
               "%s set"%str(number_set))
        raise ProofFailure(InSet(expr, number_set), assumptions, msg)

