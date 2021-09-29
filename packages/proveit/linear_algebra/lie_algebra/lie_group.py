from proveit import Function, Literal
from proveit import n
from proveit.numbers import Complex


class SU(Function):
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
        Function.__init__(self, SU._operator_, n, styles=styles)
        # self.operand = n
        self.degree = n

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
            

# SPECIAL_UNITARY = Literal(pkg, 'SU', operation_maker = lambda operands : SU(*operands))
