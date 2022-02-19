from proveit import (defaults, Literal, ExprRange, ExprTuple, ProofFailure,
                     UnsatisfiedPrerequisites, relation_prover,
                     equality_prover, TransRelUpdater)
from proveit import a, b, i, n, x, y, K, V
from proveit.logic import InSet
from proveit.abstract_algebra import GroupAdd
from proveit.linear_algebra import VecSpaces


class VecAdd(GroupAdd):
    '''
    The VecAdd operation is the default for the addition of vectors
    in a vector space.
    '''
    
    _operator_ = Literal(string_format='+', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        GroupAdd.__init__(self, VecAdd._operator_,
                          operands, styles=styles)
        self.terms = self.operands

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this ScalarMult
        expression assuming the operands have been simplified.
        
        Handles doubly-nested scalar multiplication.
        '''
        from proveit.numbers import Complex
        if all(InSet(operand, Complex).proven() for operand in self.operands):
            # If the operands are all complex numbers, this will
            # VecAdd will reduce to number Add.
            return self.number_add_reduction()
        return GroupAdd.shallow_simplification(
                self, must_evaluate=must_evaluate)

    @equality_prover('number_add_reduced', 'number_add_reduce')
    def number_add_reduction(self, **defaults_config):
        from . import scalar_add_extends_number_add
        _a = self.operands
        _i = _a.num_elements()
        return scalar_add_extends_number_add.instantiate({a:_a, i:_i})

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field,
                            **defaults_config):
        '''
        Prove that this linear combination of vectors is in a vector
        space.  The vector space may be specified or inferred via known
        memberships.  A field for the vector space must be specified.
        '''
        from proveit.linear_algebra import ScalarMult
        
        terms = self.terms
        if vec_space is None:
            # We need to find a vector space that is common to
            # all of the terms.
            candidate_vec_spaces = None
            for term in terms:
                term_vec_spaces = set(VecSpaces.yield_known_vec_spaces(
                        term, field=field))
                if hasattr(term, 'deduce_in_vec_space'):
                    try:
                        vec_space_membership = term.deduce_in_vec_space(
                                field=field)
                        term_vec_spaces.add(vec_space_membership.domain)
                    except (UnsatisfiedPrerequisites, NotImplementedError,
                            ProofFailure):
                        pass
                if candidate_vec_spaces is None:
                    candidate_vec_spaces = term_vec_spaces
                else:
                    candidate_vec_spaces.intersection_update(term_vec_spaces)
            try:
                vec_space = next(iter(candidate_vec_spaces))
            except StopIteration:
                # No known common vector space membership over the 
                # specified field.
                raise UnsatisfiedPrerequisites(
                        "%s is not known to be a vector in a vector "
                        "space over %s"%(self, field))
        field = VecSpaces.known_field(vec_space)
        all_scaled = all((isinstance(term, ScalarMult)
                          or (isinstance(term, ExprRange) and
                              isinstance(term.body, ScalarMult)))
                         for term in terms)
        if all_scaled:
            # Use a linear combination theorem since everything
            # is scaled.
            from proveit.linear_algebra.scalar_multiplication import (
                    binary_lin_comb_closure, lin_comb_closure)
            if terms.is_double():
                # Special linear combination binary case
                _a, _b = terms[0].scalar, terms[1].scalar
                _x, _y = terms[0].scaled, terms[1].scaled
                return binary_lin_comb_closure.instantiate(
                        {K:field, V:vec_space, a:_a, b:_b, x:_x, y:_y})
            else:
                # General linear combination case
                _a = []
                _x = []
                for term in terms:
                    if isinstance(term, ExprRange):
                        _a.append(ExprRange(term.parameter, term.body.scalar,
                                            term.true_start_index, term.true_end_index))
                        _x.append(ExprRange(term.parameter, term.body.scaled,
                                            term.true_start_index, term.true_end_index))
                    else:
                        _a.append(term.scalar)
                        _x.append(term.scaled)
                _n = terms.num_elements()
                return lin_comb_closure.instantiate(
                        {n:_n, K:field, V:vec_space, a:_a, x:_x})
        else:
            # Use a vector addition closure theorem.
            from . import binary_closure, closure
            if terms.is_double():
                # Special binary case
                return binary_closure.instantiate(
                        {K:field, V:vec_space, x:terms[0], y:terms[1]})
            else:
                # General case
                _n = terms.num_elements()
                return closure.instantiate(
                        {n:_n, K:field, V:vec_space, x:terms})

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factor, pull="left",
            group_factors=True, field=None, **defaults_config):
        '''
        Deduce an equality between this VecAdd expression and a
        version in which either:
        (1) the scalar factor the_factor has been factored out in
            front (or possibly out behind) to produce a new ScalarMult;
        OR
        (2) the tensor product factor the_factor has been factored
            out in front (or possible out behind) to produce a new
            TensorProd.
        For example, if
            x = VecAdd(ScalarMult(a, v1), ScalarMult(a, v2))
        then x.factorization(a) produces:
            |- x = ScalarMult(a, VecAdd(v1, v2)).
        Prove-It will need to know or be able to derive a vector space
        in which the vectors live.
        This method only works if the terms of the VecAdd are all
        ScalarMult objects or all TensorProd objects.
        In the case of all ScalarMult objects, any nested ScalarMult
        objects are first flattened if possible.
        Note: In the case of a VecAdd of all TensorProd objects,
        the lack of commutativity for tensor products limits any
        factorable tensor product factors to those occurring on the
        far left or far right of each tensor product term. Thus, for
        example, if
        x = VecAdd(TensorProd(v1, v2, v3), TensorProd(v1, v4, v5))
        we can call x.factorization(v1) to obtain
        |- x =
        TensorProd(v1, VecAdd(TensorProd(v2, v3), TensorProd(v4, v5))),
        but we cannot factor v1 our of the expression
        y = VecAdd(TensorProd(v2, v1, v3), TensorProd(v4, v1, v5))
        '''

        expr = self
        eq = TransRelUpdater(expr)

        replacements = list(defaults.replacements)

        from proveit.linear_algebra import ScalarMult, TensorProd
        from proveit.numbers import one, Mult

        # Case (1) VecAdd(ScalarMult, ScalarMult, ..., ScalarMult)
        if all(isinstance(op, ScalarMult) for op in self.operands):
            # look for the_factor in each scalar;
            # code based on Add.factorization()
            _b = []
            for _i in range(expr.terms.num_entries()):
                # remove nesting of ScalarMults
                term = expr.terms[_i].shallow_simplification().rhs
                expr = eq.update(expr.inner_expr().terms[_i].
                        shallow_simplification())
                # simplify the scalar part of the ScalarMult
                term = term.inner_expr().scalar.shallow_simplification().rhs
                expr = eq.update(expr.inner_expr().terms[_i].scalar.
                        shallow_simplification())
                if hasattr(term.scalar, 'factorization'):
                    term_scalar_factorization = term.scalar.factorization(
                        the_factor, pull, group_factors=group_factors,
                        group_remainder=True, preserve_all=True)
                    if not isinstance(term_scalar_factorization.rhs, Mult):
                        raise ValueError(
                            "Expecting right hand side of each factorization "
                            "to be a product. Instead obtained: {}".
                            format(term_scalar_factorization.rhs))
                    if pull == 'left':
                        # the grouped remainder on the right
                        _b.append(
                            ScalarMult(
                                term_scalar_factorization.rhs.operands[-1],
                                term.scaled)
                            )
                    else:
                        # the grouped remainder on the left
                        _b.append(
                            ScalarMult(
                                term_scalar_factorization.rhs.operands[0],
                                term.scaled)
                            )
                    # substitute in the factorized term
                    expr = eq.update(term_scalar_factorization.substitution(
                        expr.inner_expr().terms[_i].scalar, preserve_all=True))
                else:
                    if term.scalar != the_factor:
                        raise ValueError(
                            "Factor, %s, is not present in the term at "
                            "index %d of %s!" %
                            (the_factor, _i, self))
                    if pull == 'left':
                        replacements.append(Mult(term.scalar, one).one_elimination(1))
                    else:
                        replacements.append(Mult(one, term.scalar).one_elimination(0))
                    _b.append(ScalarMult(one, term.scaled))

            if not group_factors and isinstance(the_factor, Mult):
                factor_sub = the_factor.operands
            else:
                factor_sub = ExprTuple(the_factor)

            # pull left/right not really relevant for the ScalarMult
            # cases; this simplification step still seems relevant
            if defaults.auto_simplify:
                # Simplify the remainder of the factorization if
                # auto-simplify is enabled.
                replacements.append(VecAdd(*_b).simplification())

            from proveit import K, i, k, V, a
            # Perhaps here we could search through the operands to find
            # an appropriate VecSpace? Or maybe it doesn't matter?
            vec_space_membership = expr.operands[0].deduce_in_vec_space(
                    field=field)
            _V_sub = vec_space_membership.domain
            _K_sub = VecSpaces.known_field(_V_sub)
            _i_sub = expr.operands.num_elements()
            _k_sub = the_factor
            _a_sub = ExprTuple(*_b)

            from proveit.linear_algebra.scalar_multiplication import (
                    distribution_over_vectors)
            distribution = distribution_over_vectors.instantiate(
                    {V: _V_sub, K: _K_sub, i: _i_sub,
                     k: _k_sub, a: _a_sub}, replacements=replacements)

            # need to connect the distributed version back to the
            # original self, via a shallow_simplification() of
            # each of the ScalarMult terms resulting in the distribution
            for _i in range(len(distribution.rhs.operands.entries)):
                distribution = (
                        distribution.inner_expr().rhs.operands[_i].
                        shallow_simplify())

            eq.update(distribution.derive_reversed())

        
        # Case (2) VecAdd(TensorProd, TensorProd, ..., TensorProd)
        elif all(isinstance(op, TensorProd) for op in self.operands):
            # if hasattr(the_factor, 'operands'):
            #     print("the_factor has operands: {}".format(the_factor.operands))
            #     the_factor_tuple = the_factor.operands.entries
            # else:
            #     print("the_factor does not have operands: {}".format(the_factor))
            #     the_factor_tuple = (the_factor,)
            if isinstance(the_factor, TensorProd):
                the_factor_tuple = the_factor.operands.entries
            else:
                the_factor_tuple = (the_factor,)
            # Setting the default_field here because the field
            # used manually in the association step somehow gets lost
            VecSpaces.default_field = field
            # look for the_factor in each TensorProd appearing in
            # the VecAdd operands, looking at the left vs. right
            # sides depending on the 'pull' direction specified
            _b = [] # to hold factors left behind
            for _i in range(expr.terms.num_entries()):
                # Notice we're not ready to deal with ExprRange
                # versions of Add operands here!
                # We are also implicitly assuming that each TensorProd
                # has at least two operands
                term = expr.terms[_i]
                if hasattr(term, 'operands'):
                    term_tuple = term.operands.entries
                else:
                    term_tuple = (term,)
                if pull == 'left':
                    # look for factor at left-most-side
                    if the_factor_tuple != term_tuple[0:len(the_factor_tuple)]:
                        raise ValueError(
                            "VecAdd.factorization() expecting the_factor "
                            "{0} to appear at the leftmost side of each "
                            "addend, but {0} does not appear at the "
                            "leftmost side of the addend {1}.".
                            format(the_factor, term))
                    else:
                        # we're OK, so save away the remainder of
                        # factors from the rhs of the term,
                        # and group any multi-term factor on the left
                        if len(term_tuple[len(the_factor_tuple):])==1:
                            _b.append(term_tuple[-1])
                        else:
                            _b.append(TensorProd(
                                    *term_tuple[len(the_factor_tuple):]
                                ))
                            # then create an associated version of the
                            # expr to match the eventual thm instantiation
                            # ALSO NEED TO DO THIS FOR THE RIGHT CASE
                            expr =  eq.update(expr.inner_expr().operands[_i].
                                    association(len(the_factor_tuple),
                                        len(term_tuple)-len(the_factor_tuple),
                                        preserve_all=True))
                        # perhaps we actually don't need the assoc step?
                        # if len(the_factor_tuple) != 1:
                        #     expr = eq.update(expr.inner_expr().operands[_i].
                        #             association(0, len(the_factor_tuple),
                        #                     preserve_all=True))

                elif pull == 'right':
                    # look for factor at right-most-side
                    if the_factor_tuple != term_tuple[-(len(the_factor_tuple)):]:
                        raise ValueError(
                            "VecAdd.factorization() expecting the_factor "
                            "{0} to appear at the rightmost side of each "
                            "addend, but {0} does not appear at the "
                            "rightmost side of the addend {1}.".
                            format(the_factor, term))
                    else:
                        # we're OK, so save away the remainder of
                        # factors from the lhs of the term,
                        # and group any multi-term factor on the right
                        if len(term_tuple[0:-(len(the_factor_tuple))])==1:
                            _b.append(term_tuple[0])
                        else:
                            _b.append(TensorProd(
                                    *term_tuple[0:-(len(the_factor_tuple))]
                                ))
                            # then create an associated version of the
                            # expr to match the eventual thm instantiation
                            expr =  eq.update(expr.inner_expr().operands[_i].
                                    association(0,
                                        len(term_tuple)-len(the_factor_tuple),
                                        preserve_all=True))
                        # perhaps we actually don't need the assoc step?
                        # if len(the_factor_tuple) != 1:
                        #     expr = eq.update(expr.inner_expr().operands[_i].
                        #             association(
                        #                 len(term_tuple)-len(the_factor_tuple),
                        #                 len(the_factor_tuple),
                        #                 preserve_all=True))

                else:
                    raise ValueError(
                            "VecAdd.factorization() requires 'pull' argument "
                            "to be specified as either 'left' or 'right'.")


            # now ready to instantiate the TensorProd/VecAdd
            # theorem: tensor_prod_distribution_over_add
            # and derive it's reversed result
            from proveit.linear_algebra.tensors import (
                    tensor_prod_distribution_over_add)
            from proveit import a, b, c, i, j, k, K, V
            from proveit.numbers import zero, one, num
            # useful to get ahead of time the num of operands
            # in the_factor and define the replacement
            # if hasattr(the_factor, 'operands'):
            #     num_factor_entries = num(the_factor.operands.num_entries())
            #     factor_entries = the_factor.operands.entries
            # else:
            #     num_factor_entries = one
            #     factor_entries = (the_factor,)
            # useful to get ahead of time the num of operands
            # in the_factor and define the replacement
            if isinstance(the_factor, TensorProd):
                num_factor_entries = num(the_factor.operands.num_entries())
                factor_entries = the_factor.operands.entries
            else:
                num_factor_entries = one
                factor_entries = (the_factor,)
            # call deduce_in_vec_space() on the original self
            # instead of the current expr, otherwise we can run into
            # compications due to the associated sub-terms
            vec_space_membership = self.operands[0].deduce_in_vec_space(
                    field=field)
            _V_sub = vec_space_membership.domain
            _K_sub = VecSpaces.known_field(_V_sub)
            if pull == 'left':
                # num of operands in left the_factor
                _i_sub = num_factor_entries
                # num of operands in right factor
                _k_sub = zero
                # the actual factor operands
                _a_sub = factor_entries
                # the other side is empty
                _c_sub = ()
            elif pull == 'right':
                # left side is empty
                _i_sub = zero
                # right side has the factor
                _k_sub = num_factor_entries
                # left side is empty
                _a_sub = ()
                # right side has the factor
                _c_sub = factor_entries
            _j_sub = num(len(_b))
            _b_sub = ExprTuple(*_b)

            from proveit.linear_algebra.tensors import (
                    tensor_prod_distribution_over_add)
            impl = tensor_prod_distribution_over_add.instantiate(
                    {V: _V_sub, K: _K_sub, i: _i_sub, j: _j_sub, k: _k_sub,
                     a: _a_sub, b: _b_sub, c: _c_sub}, preserve_all=True)

            conseq = impl.derive_consequent()

            eq.update(conseq.derive_reversed())

        else:
            print("Not yet an identified case. Sorry!")

        return eq.relation

