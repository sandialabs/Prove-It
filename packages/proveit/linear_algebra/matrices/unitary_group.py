from proveit import Function, Literal, prover
from proveit import m, n, A
from proveit.logic import SetMembership
from proveit.numbers import Complex


class Unitary(Function):
    '''
    Unitary groups are Lie groups of square matrices.
    '''

    # the literal operator of the SU operation
    _operator_ = Literal(string_format='U', latex_format=r'\textrm{U}',
                         theory=__file__)

    def __init__(self, n, *, styles=None):
        '''
        Create some U(n), the special unitary of degree n.
        '''
        Function.__init__(self, Unitary._operator_, n, styles=styles)
        # self.operand = n
        self.degree = n
    
    def membership_object(self, element):
        return UnitaryMembership(element, self)
    
    def including_vec_space(self, field=None):
        '''
        The vector space that includes special unitaries is the
        matrix space of complex numbers of the appropriate size.
        '''
        from . import unitaries_are_matrices
        if field is not None and field != Complex:
            raise NotImplementedError(
                    "SU.including_vec_space only implemented for a "
                    "complex field, not %s."%field)
        subset_of_mat_space = unitaries_are_matrices.instantiate(
                {n:self.degree})
        return subset_of_mat_space.superset

class SpecialUnitary(Function):
    '''
    Special unitary groups are Lie groups of square matrices.
    '''

    # the literal operator of the SU operation
    _operator_ = Literal(string_format='SU', latex_format=r'\textrm{SU}',
                         theory=__file__)

    def __init__(self, n, *, styles=None):
        '''
        Create some SU(n), the special unitary of degree n.
        '''
        Function.__init__(self, SpecialUnitary._operator_, n, styles=styles)
        # self.operand = n
        self.degree = n
    
    def membership_object(self, element):
        return SpecialUnitaryMembership(element, self)
    
    def including_vec_space(self, field=None):
        '''
        The vector space that includes special unitaries is the
        matrix space of complex numbers of the appropriate size.
        '''
        from . import special_unitaries_are_matrices
        if field is not None and field != Complex:
            raise NotImplementedError(
                    "SU.including_vec_space only implemented for a "
                    "complex field, not %s."%field)
        subset_of_mat_space = special_unitaries_are_matrices.instantiate(
                {n:self.degree})
        return subset_of_mat_space.superset
            

class UnitaryMembership(SetMembership):
    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no SU_Membership side-effects.
        '''
        return
        yield

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to deduce that the given element is in the number set under
        the given assumptions.
        '''
        from .exponentiation import MatrixExp, U_closure
        element = self.element
        if isinstance(element, MatrixExp):
            return U_closure.instantiate({A:element.base, m:element.exponent,
                                          n: self.domain.degree})

class SpecialUnitaryMembership(SetMembership):
    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)

    def side_effects(self, judgment):
        '''
        Currently no SU_Membership side-effects.
        '''
        return
        yield

    @prover
    def conclude(self, **defaults_config):
        '''
        Try to deduce that the given element is in the number set under
        the given assumptions.
        '''
        from .exponentiation import MatrixExp, SU_closure
        element = self.element
        if isinstance(element, MatrixExp):
            return SU_closure.instantiate({A:element.base, m:element.exponent,
                                           n: self.domain.degree})
            
