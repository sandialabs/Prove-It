from proveit._core_.expression.expr import MakeNotImplemented
from .expr_tuple import ExprTuple
from .expr_array import ExprArray, var_array
from proveit.decorators import relation_prover, equality_prover


class VertExprArray(ExprArray):
    '''
    An ExprArray represented in column-major order.
    '''
    
    def __init__(self, *columns, styles=None):
        '''
        Initialize a VertExprArray from an iterable over ExprTuple
        objects or Expressions that represent ExprTuples, each 
        representing a column of the 2-dimensional array.
        '''
        ExprArray.__init__(self, *columns, styles=styles)

    @classmethod
    def _make(sub_class, core_info, sub_expressions, *, styles):
        if sub_class != VertExprArray:
            raise MakeNotImplemented(sub_class)
        if len(core_info) != 1 or core_info[0] != 'ExprTuple':
            raise ValueError("A VertExprArray is an ExprTuple of ExprTuples, "
                             "so the ExprArray core_info should contain "
                             "exactly one item: 'ExprTuple'")
        return VertExprArray(*sub_expressions, styles=styles)

    def get_latex_formatted_cells(self, orientation='vertical',
                                  vertical_explicit_cell_latex_fn=None,
                                  horizontal_explicit_cell_latex_fn=None,
                                  format_cell_entries=None,
                                  col_row_to_latex_kwargs=None):
        return ExprArray.get_latex_formatted_cells(
                self, orientation,
                vertical_explicit_cell_latex_fn
                =vertical_explicit_cell_latex_fn,
                horizontal_explicit_cell_latex_fn
                =horizontal_explicit_cell_latex_fn,
                # col/row are switched in name, but either way
                # it is (outer index, inner index) order.
                row_col_to_latex_kwargs=col_row_to_latex_kwargs)
    
    def get_format_row_element_positions(self):
        return self.get_inner_format_cell_element_positions()
    
    def latex(self, fence=False, **kwargs):
        return ExprArray.latex(self, orientation='vertical', fence=fence,
                               **kwargs)

    def _config_latex_tool(self, lt):
        ExprArray._config_latex_tool(self, lt)
        if 'multirow' not in lt.packages:
            lt.packages.append('multirow')

    @equality_prover('equated', 'equate')
    def deduce_equality(self, equality, **defaults_config):
        from proveit.core_expr_types.expr_arrays import (
                varray_eq_via_elem_eq_thm)
        return ExprTuple.deduce_equality(
                self, equality, eq_via_elem_eq_thm=varray_eq_via_elem_eq_thm)

    @relation_prover
    def not_equal(self, other_tuple, **defaults_config):
        '''
        Prove and return this ExprArray not equal to the other
        ExprArray.
        '''
        from proveit.core_expr_types.expr_arrays import (
                varray_neq_with_diff_len, varray_neq_via_any_elem_neq)
        return ExprTuple.not_equal(
                self, other_tuple, 
                neq_with_diff_len_thm=varray_neq_with_diff_len,
                neq_via_any_elem_neq_thm=varray_neq_via_any_elem_neq)


vert_var_array = (
        lambda var, start_index_or_indices, end_index_or_indices :
            var_array(var, start_index_or_indices, end_index_or_indices,
                      array_type=VertExprArray))