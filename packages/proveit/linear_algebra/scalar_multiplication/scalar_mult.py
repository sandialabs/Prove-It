from proveit import (Operation, Literal, relation_prover,
                     equality_prover, UnsatisfiedPrerequisites)
from proveit import a, x, K, V, alpha, beta
from proveit.logic import InSet
from proveit.abstract_algebra import plus, times
from proveit.linear_algebra import VecSpaces

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
        
        Handles doubly-nested scalar multiplication.
        '''
        if isinstance(self.scaled, ScalarMult):
            # Reduce a doubly nested scalar multiplication.
            return self.double_scaling_reduction(preserve_all=True)
        return Operation.shallow_simplification(
                self, must_evaluate=must_evaluate)
    
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
        _plus = _K.plus_operator
        _times = _K.times_operator
        return doubly_scaled_as_singly_scaled.instantiate(
                {plus:_plus, times:_times, K:_K, V:_V, 
                 x:_x, alpha:_alpha, beta:_beta})        

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
            try:
                vec_space = next(VecSpaces.yield_known_vec_spaces(
                        self.scaled, field=field))
            except StopIteration:
                # No known vector space membership over the specified
                # field.
                raise UnsatisfiedPrerequisites(
                        "%s is not known to be a vector in a vector "
                        "space over %s"%(self.scaled, field))
        return scalar_mult_closure.instantiate(
                {K:field, V:vec_space, a:self.scalar, x:self.scaled})