from proveit import Literal, Operation, NamedExprs, prover
from proveit import m, n
from proveit.logic import SetMembership


class MatrixSpace(Operation):
    '''
    A MatrixSpace represents the set of matrices with a specific
    number of rows and columns applicable over a specific field. 
    '''
    _operator_ = Literal(string_format=r'MSpace', theory=__file__)
    
    # Map elements to their known memberships in a matrix space.
    known_memberships = dict()
    
    def __init__(self, field, rows, columns, *, styles=None):
        '''
        Create F^{m x n} as the MatrixSpace for field F with
        
        '''
        Operation.__init__(self, MatrixSpace._operator_,
                           NamedExprs([('field', field), 
                                       ('rows', rows),
                                       ('columns', columns)]), 
                           styles=styles)
        self.field = field
        self.rows = rows
        self.columns = columns

    def formatted(self, format_type, **kwargs):
        times_operator = 'x' if format_type == 'string' else r'\times'
        return self.field.formatted(format_type, fenced=True) + (
                "^{%s %s %s}"%(
                        self.rows.formatted(format_type, fence=True),
                        times_operator,
                        self.columns.formatted(format_type, fence=True)))

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def membership_object(self, element):
        return MatrixSpaceMembership(element, self)

    def including_vec_space(self, *, field=None, **defaults_config):
        '''
        Return a vector space over the given field which includes
        this matrix space.
        '''
        from proveit.numbers import Rational, Real, Complex
        if field is None or field==self.field:
            return self
        elif ((field == Complex and subset.base in (Rational, Real))
              or (field == Real and subset.base == Rational)):
            return MatrixSpace(field, self.rows, self.columns)

    @prover
    def deduce_as_vec_space(self, **defaults_config):
        '''
        Prove that this matrix space is a vector space (contained
        in the class of vector spaces over some field).  Handles
        the case in which the matrix space field is rational, real,
        or complex (where VecAdd and ScalarMult are defined in a
        standard manner).
        '''        
        from proveit.numbers import Rational, Real, Complex
        from . import (rational_matrix_space_is_vec_space,
                       real_matrix_space_is_vec_space,
                       complex_matrix_space_is_vec_space)
        _m, _n = self.rows, self.columns
        if self.field == Rational:
            return rational_matrix_space_is_vec_space.instantiate(
                    {m:_m, n:_n})
        elif self.field == Real:
            return real_matrix_space_is_vec_space.instantiate(
                    {m:_m, n:_n})
        elif self.field == Complex:
            return complex_matrix_space_is_vec_space.instantiate(
                    {m:_m, n:_n})
        raise NotImplementedError(
                "Cannot deduce that the matrix space over %s "
                "is a vector space"%self.field)


class MatrixSpaceMembership(SetMembership):
    '''
    Defines methods that apply to InSet(element, LinMap(X, Y))
    objects via InClass.__getattr__ which calls 
    LinMap.membership_object(element)
    to return a LinMapMembership object.    
    '''

    def __init__(self, element, domain):
        SetMembership.__init__(self, element, domain)
        
    def side_effects(self, judgment):
        MatrixSpace.known_memberships.setdefault(
                self.element, set()).add(judgment)
        return # generator yielding nothing
        yield


