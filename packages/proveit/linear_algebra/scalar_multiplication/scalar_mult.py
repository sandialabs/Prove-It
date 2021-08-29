from proveit import (Operation, Literal, relation_prover,
                     UnsatisfiedPrerequisites)
from proveit import a, x, K, V
from proveit.logic import InSet
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