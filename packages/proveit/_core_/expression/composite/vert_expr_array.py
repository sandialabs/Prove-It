from .expr_array import ExprArray

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

    def get_latex_formatted_cells(self, orientation='vertical',
                                  vertical_explicit_cell_latex_fn=None,
                                  horizontal_explicit_cell_latex_fn=None,
                                  format_cell_entries=None,
                                  **cell_latex_kwargs):
        return ExprArray.get_latex_formatted_cells(
                self, orientation,
                vertical_explicit_cell_latex_fn
                =vertical_explicit_cell_latex_fn,
                horizontal_explicit_cell_latex_fn
                =horizontal_explicit_cell_latex_fn,
                format_cell_entries=format_cell_entries,
                **cell_latex_kwargs)
    
    def get_format_row_element_positions(self):
        return self.get_inner_format_cell_element_positions()
    
    def latex(self, fence=False, **kwargs):
        return ExprArray.latex(self, orientation='vertical', fence=fence,
                               **kwargs)

    def _config_latex_tool(self, lt):
        ExprArray._config_latex_tool(self, lt)
        if 'multirow' not in lt.packages:
            lt.packages.append('multirow')
