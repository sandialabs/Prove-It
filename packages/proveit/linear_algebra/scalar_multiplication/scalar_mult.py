from proveit import (Operation, Literal, relation_prover,
                     equality_prover, TransRelUpdater, UnsatisfiedPrerequisites)
from proveit import a, b, x, K, V, alpha, beta
from proveit.logic import InSet
from proveit.abstract_algebra import plus, times
from proveit.linear_algebra import VecSpaces
from proveit.numbers import one

class ScalarMult(Operation):
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

    def __init__(self, scalar, scaled, *, styles=None):
        r'''
        Product between a scalar and a matrix (or vector).
        '''
        Operation.__init__(self, ScalarMult._operator_, [scalar, scaled],
                           styles=styles)
        self.scalar = scalar
        self.scaled = scaled

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this ScalarMult
        expression assuming the operands have been simplified.
        Handles:
        (1) Multiply-nested scalar multiplication -- for example,
            taking ScalarMult(a, ScalarMult(b, ScalarMult(c, v)))
            to ScalarMult(Mult(a, b, c), v)
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

        # (1) Simplify multiply-nested scalar multiplications
        # if isinstance(self.scaled, ScalarMult):
        if isinstance(expr.scaled, ScalarMult):
            # Reduce multiply-nested scalar multiplications.
            # return self.multi_scaling_reduction(preserve_all=True)
            expr = eq.update(self.multi_scaling_reduction(preserve_all=True))

        # (2) Simplify multiplicative idenity
        if expr.scalar == one:
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
        _V = VecSpaces.known_vec_space(_x)
        _K = VecSpaces.known_field(_V)
        _alpha = self.scalar
        _beta =  self.scaled.scalar
        return doubly_scaled_as_singly_scaled.instantiate(
                {K:_K, V:_V, x:_x, alpha:_alpha, beta:_beta})

    @equality_prover('multi_scaling_reduced', 'multi_scaling_reduce')
    def multi_scaling_reduction(self, **defaults_config):
        expr = self

        # A convenience to allow successive updates to the equation via
        # transitivities (starting with self=self).
        eq = TransRelUpdater(self)

        while (isinstance(expr.scaled, ScalarMult) and
               isinstance(expr.scaled.scaled, ScalarMult)):
            # For all but the last reduction, use preserve_all=True.
            expr = eq.update(expr.double_scaling_reduction(preserve_all=True))
        
        if isinstance(expr.scaled, ScalarMult):
            # For the last reduction, we may allow simplification.
            expr = eq.update(expr.double_scaling_reduction())

        return eq.relation

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
