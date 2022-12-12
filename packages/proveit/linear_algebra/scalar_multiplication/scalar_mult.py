from proveit import (Operation, Literal, prover, relation_prover,
                     SimplificationDirectives,
                     equality_prover, TransRelUpdater, UnsatisfiedPrerequisites)
from proveit import a, b, x, H, K, V, alpha, beta
from proveit.logic import InSet, Equals
from proveit.numbers import one, Complex
from proveit.abstract_algebra import plus, times
from proveit.linear_algebra import (
        VecSpaces, VecOperation, deduce_canonically_equal)

class ScalarMult(VecOperation):
    '''
    The ScalarMult operation is the default for the scalar 
    multiplication of a vector and may also be used for scalar
    multiplication of a matrix (in the same manner since matrix
    spaces are vector spaces).
    '''
    # the literal operator of the MatrixProd operation
    # perhaps use SCALAR_PROD for string?
    # latex_format try using \; in place of a blank space
    _operator_ = Literal(string_format=r'*', latex_format=r'\cdot',
                         theory=__file__)

    _simplification_directives_ = SimplificationDirectives()

    def __init__(self, scalar, scaled, *, styles=None):
        r'''
        Product between a scalar and a matrix (or vector).
        '''
        Operation.__init__(self, ScalarMult._operator_, [scalar, scaled],
                           styles=styles)
        self.scalar = scalar
        self.scaled = scaled

    def _build_canonical_form(self):
        '''
        Returns the canonical form of this ScalarMult, combining
        scalars as possible.
        '''
        from proveit.numbers import one, Mult
        canonical_scalar = self.scalar.canonical_form()
        canonical_scaled = self.scaled.canonical_form()
        if isinstance(canonical_scaled, ScalarMult):
            combined_scalar = Mult(canonical_scalar, 
                                   canonical_scaled.scalar)
            canonical_scalar = combined_scalar.canonical_form()
            canonical_scaled = canonical_scaled.scaled
        if canonical_scalar == one:
            return canonical_scaled
        # We can only do the following if we know the vector space.
        # Not sure the best way to handle this since the canonical
        # form should not depend upon assumptions:
        #elif canonical_scalar == zero:
        #    return VecZero
        return ScalarMult(canonical_scalar, canonical_scaled)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this ScalarMult
        expression assuming the operands have been simplified.
        Handles:
        (1) Doubly-nested scalar multiplication -- for example,
            taking ScalarMult(a, ScalarMult(b, v))
            to ScalarMult(ScalarMult(a, b), v)
        (2) ScalarMult identity -- for example, taking ScalarMult(1, v)
            to v.
        '''
        from proveit.numbers import Complex
        if (InSet(self.scalar, Complex).proven() 
                and InSet(self.scaled, Complex).proven()):
            # If the operands are both complex numbers, this will
            # ScalarMult will reduce to number multiplication.
            return self.number_mult_reduction()
        
        expr = self
        # A convenience to allow successive updating of the equation
        # via transitivities (starting with self=self).
        eq = TransRelUpdater(self)

        # (1) Simplify doubly-nested scalar multiplication
        if isinstance(expr.scaled, ScalarMult):
            # Reduce a double-nested scalar multiplication.
            expr = eq.update(self.double_scaling_reduction())

        # (2) Simplify multiplicative identity
        #     (if expr is still a ScalarMult)
        if isinstance(expr, ScalarMult) and expr.scalar == one:
            expr = eq.update(expr.scalar_one_elimination(preserve_all=True))

        return eq.relation

    @equality_prover('number_mult_reduced', 'number_mult_reduce')
    def number_mult_reduction(self, **defaults_config):
        from . import scalar_mult_extends_number_mult
        return scalar_mult_extends_number_mult.instantiate(
                {a:self.scalar, b:self.scaled})
    
    @equality_prover('double_scaling_reduced', 'double_scaling_reduce')
    def double_scaling_reduction(self, **defaults_config):
        from . import doubly_scaled_as_singly_scaled
        if not isinstance(self.scaled, ScalarMult):
            raise ValueError("'double_scaling_reduction' is only applicable "
                             "for a doubly nested ScalarMult")
        # Reduce doubly-nested ScalarMult
        _x = self.scaled.scaled
        # _V = VecSpaces.known_vec_space(_x)
        # the following is a little klunky, but trying to avoid the
        # use of a default field=Real if we're actually dealing with
        # complex scalars somewhere in the vector
        from proveit import free_vars
        if any([InSet(elem, Complex).proven() for
                elem in free_vars(self)]):
            _V = VecSpaces.known_vec_space(self, field=Complex)
        else:
            _V = VecSpaces.known_vec_space(self)
        _K = VecSpaces.known_field(_V)
        _alpha = self.scalar
        _beta =  self.scaled.scalar
        return doubly_scaled_as_singly_scaled.instantiate(
                {K:_K, V:_V, x:_x, alpha:_alpha, beta:_beta})

    @equality_prover('scalar_one_eliminated', 'scalar_one_eliminate')
    def scalar_one_elimination(self, **defaults_config):
        '''
        Equivalence method that derives a simplification in which
        a single scalar multiplier of 1 is eliminated.
        For example, letting v denote a vector element of some VecSpace,
        then ScalarMult(one, v).scalar_one_elimination() would return
            |- ScalarMult(one, v) = v
        Will need to know that v is in VecSpaces(K) and that the
        multiplicative identity 1 is in the field K. This might require
        assumptions or pre-proving of a VecSpace that contains the
        vector appearing in the ScalarMult expression.
        '''
        from proveit.numbers import one
        # from . import elim_one_left, elim_one_right
        from . import one_as_scalar_mult_id

        # The following seems silly -- if the scalar is not 1, just
        # return with no change instead?
        if self.scalar != one:
            raise ValueError(
                "For ScalarMult.scalar_one_elimination(), the scalar "
                "multiplier in {0} was expected to be 1 but instead "
                "was {1}.".format(self, self.scalar))

        # obtain the instance params:
        # _K is the field; _V is the vector space over field _K;
        # and _v is the vector in _V being scaled
        _K, _v, _V = one_as_scalar_mult_id.all_instance_params()

        # isolate the vector portion
        _v_sub = self.scaled

        # Find a containing vector space V in the theorem.
        # This may fail!
        _V_sub = list(VecSpaces.yield_known_vec_spaces(_v_sub))[0]

        # Find a vec space field, hopefully one that contains the mult
        # identity 1. This may fail!
        _K_sub = list(VecSpaces.yield_known_fields(_V_sub))[0]

        # If we made it this far, can probably instantiate the theorem
        # (although it could still fail if 1 is not in the field _K_sub)
        return one_as_scalar_mult_id.instantiate(
                {_K: _K_sub, _v: _v_sub, _V: _V_sub})

        # if self.operands.is_double():
        #     if idx == 0:
        #         return elim_one_left.instantiate({x: self.operands[1]})
        #     else:
        #         return elim_one_right.instantiate({x: self.operands[0]})
        # _a = self.operands[:idx]
        # _b = self.operands[idx + 1:]
        # _i = _a.num_elements()
        # _j = _b.num_elements()
        # return elim_one_any.instantiate({i: _i, j: _j, a: _a, b: _b})       

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field,
                            **defaults_config):
        '''
        Prove that this scaled vector is in a vector space.  The vector
        space may be specified or inferred via known memberships.  
        A field for the vector space must be specified.
        '''
        from . import scalar_mult_closure
        if vec_space is None:
            # No vector space given, so we'll have to look for
            # a known membership of 'scaled' in a vector space.
            # This may be arbitrarily chosen.
            vec_space = VecSpaces.known_vec_space(
                        self.scaled, field=field)
            field = VecSpaces.known_field(vec_space)
        return scalar_mult_closure.instantiate(
                {K:field, V:vec_space, a:self.scalar, x:self.scaled})
    
    @prover
    def compute_norm(self, **defaults_config):
        '''
        Proves ‖a v‖ = |a| ‖v‖.
        '''
        from proveit.linear_algebra.inner_products import scaled_norm
        vec_space = VecSpaces.known_vec_space(self.scaled)
        field = VecSpaces.known_field(vec_space)
        return scaled_norm.instantiate(
                {K:field, H:vec_space, alpha:self.scalar, x:self.scaled})

    def readily_factorable(self, factor, *, pull):
        '''
        Return True if 'factor' may be easily factored from this
        VecAdd, pulling either to the 'left' or the 'right'.
        If pulling to the 'left', the factor must be at the front
        of any tensor product of vectors.  If pulling to the 'right', 
        the factor must be at the back of any tensor product of vectors.
        '''
        from proveit.linear_algebra import readily_factorable
        if self == factor:
            return True

        # Put the 'self' and the candidate factor in canonical form 
        # which will put scalars in the front.
        canonical_self = self.canonical_form()
        if canonical_self.factors.num_entries()==0:
            return False # Empty tensor product cannot be factored.
        canonical_factor = factor.canonical_form()
        if isinstance(canonical_factor, ScalarMult):
            if not isinstance(canonical_self, ScalarMult):
                # Nothing to factor the scalar from.
                return False
            if not readily_factorable(canonical_self.scalar,
                                      canonical_factor.scalar):
                # Can't factor the scalar part.
                return False
            canonical_factor = canonical_factor.scaled
        if isinstance(canonical_self, ScalarMult):
            # We've addressed any scalar part.
            canonical_self = canonical_self.scaled
        return canonical_self.readily_factorable(canonical_factor)

    @equality_prover('factorized', 'factor')
    def factorization(self, the_factor, *, pull,
            group_factors=True, group_remainder=False,
            field=None, **defaults_config):
        '''
        Factor 'the_factor' from this ScalarMult.

        A scalar factor may be pulled to the left, a vector factor
        may be pulled to the right, or a portion of a tensor product
        may be pulled to either side.  These are examples for each
        of these cases respectively:
            (a b c) x = (b c) (a x) = ((b c) a) x = (b c a) x
            a x⊗y⊗z = (a x)⊗(y⊗z) = (a x)⊗y⊗z
            a x⊗(b y)⊗z = (b x)⊗(a y⊗z)
            a x⊗(b y)⊗z = (b a x) ⊗ (y⊗z)
            a b x⊗y⊗z = (b x)⊗(a y⊗z)
        
        Different possibilities of group_factors=True/False and 
        group_remainder=True/False are shown via multiple equalities
        in a line.
        '''
        import proveit.numbers
        from proveit.numbers import (
                Mult, one, remove_common_factors)
        from proveit.linear_algebra import TensorProd
        
        the_factor_cf = the_factor.canonical_form()
        if self.canonical_form() == the_factor_cf:
            # Trivial case of factoring the entire ScalarMult.
            return deduce_canonically_equal(self, the_factor, field=field)
        
        if proveit.numbers.readily_factorable(self.scalar, the_factor):
            # Factor just from the scalar part.
            if pull != 'left':
                raise ValueError("Scalars must be pulled to the 'left' "
                                 "when factoring from vectors")
            if self.scalar.canonical_form() == the_factor_cf:
                # Simple case of factoring the entire scalar.
                desired = ScalarMult(the_factor, self.scaled)
            else:
                remaining_scalar = remove_common_factors(self.scalar, 
                                                         the_factor)
                remaining_scalars = (
                        remaining_scalar.factors if isinstance(
                                remaining_scalar, Mult)
                        else (remaining_scalar,))
                if group_remainder:
                    # e.g., (a b c) x = (b c) (a x)
                    desired = ScalarMult(
                            the_factor, ScalarMult(remaining_scalar,
                                                   self.scaled))
                elif group_factors:
                    # e.g., (a b c) x = ((b c) a) x
                    desired = ScalarMult(
                            Mult(the_factor, *remaining_scalars),
                            self.scaled)
                else:
                    # e.g., (a b c) x = (b c a) x
                    if isinstance(the_factor, Mult):
                        the_factor = the_factor.factors
                    desired = ScalarMult(
                            Mult(the_factor, *remaining_scalars),
                            self.scaled)
            return deduce_canonically_equal(self, desired, field=field)

        # Put the factor in its canonical form and separate out any
        # of its scalar factors.
        factor_scalar, factor_scaled = canonical_scalar_and_scaled(
                the_factor)
        print('factor_scalar', factor_scalar, 'factor_scaled', factor_scaled)
        
        remaining_scalar = remove_common_factors(
                self.scalar, factor_scalar)
        inner_factor_scalar = remove_common_factors(factor_scalar,
                                                    self.scalar)
        # We can put this in canonical form since it doesn't
        # go directly into the end result.
        inner_factor_scalar = inner_factor_scalar
        print('remaining_scalar', remaining_scalar)
        print('inner_factor_scalar', inner_factor_scalar)
        print('inner_factor_scalar_cf', inner_factor_scalar.canonical_form())
        if inner_factor_scalar != one:
            inner_factor = ScalarMult(
                    inner_factor_scalar, factor_scaled)
        else:
            inner_factor = factor_scaled
        
        # Factor from the vector part so we can get the remainder
        # that we will combine with the remaining part of the scalar.
        factorization_of_vec = self.inner_expr().scaled.factorization(
                inner_factor, pull=pull, field=field, group_factors=True,
                group_remainder=(group_remainder and
                                 remaining_scalar==one))
        vec_factored = factorization_of_vec.rhs.scaled
        
        
        if pull=='left':
            if isinstance(vec_factored, TensorProd):
                vec_remainder = TensorProd(*vec_factored[1:])
                if remaining_scalar == one:
                    # e.g., a x⊗(b y)⊗z = (b a x) ⊗ (y⊗z)
                    desired = TensorProd(the_factor, vec_remainder)
                else:
                    # e.g., a x⊗(b y)⊗z = (b x)⊗(a y⊗z)
                    desired = TensorProd(
                            the_factor, ScalarMult(remaining_scalar, 
                                                   vec_remainder))
            else:
                raise ValueError(
                        "Cannot pull a vector factor to the 'left' "
                        "unless it is a portion of a tensor product.")
        elif pull=='right':
            if isinstance(vec_factored, TensorProd):
                vec_remainder_factors = vec_factored.factors[:-1]
                if len(vec_remainder_factors) > 1:
                    vec_remainder = TensorProd(*vec_remainder_factors)
                elif len(vec_remainder_factors) == 1:
                    vec_remainder = vec_remainder_factors[0]
                    if remaining_scalar == one:
                        # e.g., a x⊗(b y)⊗z = (b x)⊗(a y⊗z)
                        desired = TensorProd(vec_remainder, the_factor)
                    else:
                        # e.g., a b x⊗y⊗z = (b x)⊗(a y⊗z)
                        desired = TensorProd(
                                ScalarMult(remaining_scalar, 
                                           vec_remainder), the_factor)
                elif remaining_scalar == one:
                    desired = the_factor
                else:
                    desired = ScalarMult(remaining_scalar, the_factor)
            elif isinstance(vec_factored, ScalarMult):
                if remaining_scalar==one:
                    # e.g., a (b c x) = (b c) (a x)
                    desired = ScalarMult(vec_factored.scalar, the_factor)
                else:
                    # e.g., a (b c x) = (a (b c)) x, pull x to right
                    desired = ScalarMult(
                            Mult(remaining_scalar, vec_factored.scalar), 
                            the_factor)
            else:
                assert False, ("%s is not an expected factorized form"
                               %vec_factored)
        else:
            raise ValueError("'pull' must be 'left' or 'right', not %s"
                             %pull)
        print('the_factor', the_factor, 'vec_factored', vec_factored, 
              'remaining_scalar', remaining_scalar)

        print('self', self, 'desired', desired)

        # We should be able to prove that are desired form is equal
        # to the factorization_of_vec form by having the same canonical
        # form.
        return factorization_of_vec.apply_transitivity(
                deduce_canonically_equal(factorization_of_vec.rhs,
                                         desired, field=field))
        

def canonical_scalar_and_scaled(expr):
    canonical_form = expr.canonical_form()
    if isinstance(canonical_form, ScalarMult):
        return canonical_form.scalar, canonical_form.scaled
    else:
        return one, canonical_form
