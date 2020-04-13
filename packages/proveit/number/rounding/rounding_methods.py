from proveit import defaults, TransRelUpdater, USE_DEFAULTS

def apply_roundingElimination(expr, roundingEliminationThm,
                              assumptions=USE_DEFAULTS):
    '''
    For the trivial case of Round(x) where the operand x is already
    an integer, derive and return this Round expression equated
    with the operand itself: Round(x) = x. Assumptions may be
    necessary to deduce necessary conditions (for example, that x
    actually is an integer) for the simplification.
    This method is utilized by the doReducedSimplification() method
    only after the operand x is verified to already be proven
    (or assumed) to be an integer.
    For the case where the operand is of the form x = real + int,
    see the roundingExtraction() method.
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
        For the case of Round(x) where the operand x = x_real + x_int,
        derive and return Round(x) = Round(x_real) + int (thus
        'extracting' the integer component out from the Round() fxn).
        The idx_to_extract is the zero-based index of the item in the
        operands of an Add(a, b, …, n) expression to attempt to extract.
        Assumptions may be necessary to deduce necessary conditions
        (for example, that x_int actually is an integer) for the
        simplification.
        This method is utilized by the doReducedSimplification() method
        only after the operand x is verified to already be proven
        (or assumed) to be of the form x = x_real + x_int.
        For the case where the entire operand x is itself an integer,
        see the roundingElimination() method.

        This works only if the operand x is an instance of the Add
        class at its outermost level, e.g. x = Add(a, b, …, n). The
        operands of that Add class can be other things, but the
        extraction is guaranteed to work only if the inner operands
        a, b, etc., are simple.
        '''
        from proveit._common_ import n, x, y
        from proveit.number import Add
        # from ._theorems_ import roundOfRealPlusInt

        # among other things, convert any assumptions=None
        # to assumptions=() to avoid later len() errors
        assumptions = defaults.checkedAssumptions(assumptions)

        # expr = self

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
        # from ._theorems_ import roundOfInteger, roundOfRealPlusInt

        # among other things, convert any assumptions=None
        # to assumptions=()
        assumptions = defaults.checkedAssumptions(assumptions)

        #-- -------------------------------------------------------- --#
        #-- Case (1): F(x) where entire operand x is known or        --#
        #--           assumed to be an Integer.                      --#
        #-- -------------------------------------------------------- --#
        if InSet(expr.operand, Integers).proven(assumptions=assumptions):
            # Entire operand is known to be or assumed to be an integer
            # so we can simply remove the Round() wrapper
            return expr.roundingElimination(assumptions)
        #-- -------------------------------------------------------- --#
        #-- Case (2): F(x) = F(Add(a,b,...,n)), where operand x is   --#
        #--           an Add object, not known or assumed to be an   --#
        #--           an int, but addends might be reals and ints    --#
        #-- -------------------------------------------------------- --#
        elif isinstance(expr.operand, Add):
            # Try to partition all suboperands into ints vs. reals
            tempExpr = expr
            # for convenience while updating our equation
            eq = TransRelUpdater(tempExpr, assumptions)

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
            if len(indices_of_unknowns) == 0:
                # each addend is an int or a real, so we should be able
                # to rearrange and partition the addends as such
                original_addends = list(subops)
                desired_order_by_index = list(
                        indices_of_reals_not_ints+indices_of_known_ints)
                # commute to put reals first, followed by ints
                for i in range(len(original_addends)):
                    init_idx = tempExpr.operand.operands.index(
                            original_addends[desired_order_by_index[i]])
                    tempExpr = eq.update(
                            tempExpr.innerExpr().operand.commutation(
                                    init_idx, i, assumptions=assumptions))

                # associate the reals
                if len(indices_of_reals_not_ints) > 1:
                    # associate those elements (already re-arranged to
                    # be at the front of the operand.operands):
                    tempExpr = eq.update(
                            tempExpr.innerExpr().operand.association(
                                    0, len(indices_of_reals_not_ints),
                                    assumptions=assumptions))
                # associate the ints
                if len(indices_of_known_ints) > 1:
                    # associate those elements (already re-arranged to
                    # be at the end of the operand.operands):
                    tempExpr = eq.update(
                            tempExpr.innerExpr().operand.association(
                                    1, len(indices_of_known_ints),
                                    assumptions=assumptions))

                tempExpr = eq.update(
                    tempExpr.roundingExtraction(1, assumptions))
                return eq.relation

            else:
                list_of_unknowns = [subops[i] for i in indices_of_unknowns]
                msg = ("In attempting f(x).apply_reducedSimplification, "
                       "the operands {} are not assumed or proven to be "
                       "Integers or Reals.".
                       format(list_of_unknowns))
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