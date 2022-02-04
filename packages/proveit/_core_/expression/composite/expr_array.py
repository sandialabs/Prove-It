from .expr_tuple import ExprTuple
from .expr_range import ExprRange
from proveit._core_.expression.expr import MakeNotImplemented
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_.defaults import USE_DEFAULTS


class ExprArray(ExprTuple):
    '''
    An ExprArray represents a 2-dimensional array.  It is simply
    an ExprTuple of ExprTuples (or Expressions representing ExprTuples).
    By default, each inner ExprTuple is a row of the array (row-major
    order).  For the opposite orientation (column-major order), use
    VertExprArray.
    '''

    def __init__(self, *rows_or_columns, styles=None):
        '''
        Initialize an ExprArray from an iterable over ExprTuple
        objects or Expressions that represent ExprTuples, each
        representing a row (or a column if it is a VertExprArray).
        '''
        ExprTuple.__init__(self, *rows_or_columns, styles=styles)

    @classmethod
    def _make(sub_class, core_info, sub_expressions, *, styles):
        if sub_class != ExprArray:
            raise MakeNotImplemented(sub_class)
        if len(core_info) != 1 or core_info[0] != 'ExprTuple':
            raise ValueError("An ExprArray is an ExprTuple of ExprTuples, "
                             "so the ExprArray core_info should contain "
                             "exactly one item: 'ExprTuple'")
        return ExprArray(*sub_expressions, styles=styles)

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        call_strs = []
        justification = self.get_style('justification')
        if justification != 'center':
            call_strs.append('with_justification("' + justification + '")')
        return call_strs

    def style_options(self):
        '''
        Return the StyleOptions object for this ExprArray.
        '''
        options = StyleOptions(self)
        options.add_option(
            name='justification',
            description=("justify to the 'left', 'center', or 'right' "
                         "in the array cells"),
            default='center',
            related_methods='with_justification')
        return options
    
    def with_justification(self, justification):
        return self.with_styles(justification=justification)

    def flat(self):
        '''
        Returns the contents of the array as a flattened ExprTuple.
        For example, instead of returning [[A, B, C}, [D, E, F]]
        - which displays as
         A B C
         D E F
        it would return [A, B, C, D, E, F]
        '''
        entries = []
        for entry in self:
            if isinstance(entry, ExprTuple):
                for value in entry:
                    entries.append(value)
            else:
                entries.append(value)
        return ExprTuple(entries)
    
    def get_format_cell_entries(self, format_cell_entries=None):
        '''
        Returns a list of (for the most part) lists of entries in 
        correspondence with each format cell of this ExprArray.  It is
        possible to have an entry that represents an entire inner list
        (an entire row, or column in the case of a VertExprArray).
        Each entry is a pair or triple tuple with the first item 
        containing an Expression corresponding to the entry and the
        others indicating the role of the cell.  It will be composed
        of the role within the outer ExprTuple and the role within the 
        inner ExprTuple respectively with the following exception.
        For a ExprRange of ExprTuples of ExprRanges with explicit
        parameterization, the explicit parameterization will be
        shown compactly only in the center of the range of ranges
        but will be made implicit in the cells above/below/left/right.
                
        The 'role' information will be used to determine how to format
        the cell with respect to using horizontal/vertical ellipses,
        etc.

        If 'format_cell_entries' is provided, append to it rather
        than creating a new list.
        '''
        # Construct the list of (for the most part) lists of entries
        # first by simply composing outer and inner roles.
        # Remember coordinates of entries that are 'explicit' outside
        # and inside -- we'll edit their surrounding entries next.
        if format_cell_entries is None:
            format_cell_entries = []
        else:
            if not isinstance(format_cell_entries, list):
                raise TypeError("Expecting 'format_cell_entries' to be a "
                                "list")
        doubly_explicit_coordinates = []
        for _i, outer_entry in enumerate(
                ExprTuple.get_format_cell_entries(self)):
            outer_expr, outer_role = outer_entry
            orig_outer_expr = outer_expr
            if isinstance(outer_expr, ExprRange):
                outer_expr = outer_expr.innermost_body()
                # But then wrap the inner_expr's below with the
                # ExprRange's -- something like that??? TODO
            if isinstance(outer_expr, ExprTuple):
                # An explicit inner list.
                inner_format_cell_entries = []
                for _j, inner_entry in enumerate(
                        outer_expr.get_format_cell_entries()):
                    inner_expr, inner_role = inner_entry
                    if (orig_outer_expr != outer_expr and
                            not isinstance(inner_expr, ExprRange)):
                        # The other_expr was originally an ExprRange
                        # but the inner_expr is not.  In this case, we
                        # want to show the entry expr as an ExprRange
                        # for the outer orientation with this inner
                        # exrpession.  That is, lLet's wrap the 
                        # inner_expr with the ExprRange(s) in the same
                        # way as the original ExprRange.
                        _expr_ranges = [orig_outer_expr]
                        while isinstance(_expr_ranges[-1].body, ExprRange):
                            _expr_ranges.append(_expr_ranges[-1].body)
                        for _er in reversed(_expr_ranges):
                            inner_expr = ExprRange(
                                    _er.parameter, inner_expr,
                                    _er.start_index, _er.end_index)
                            inner_expr = inner_expr.with_mimicked_style(_er)
                    # Compose outer and inner roles.
                    inner_format_cell_entries.append(
                            (inner_expr, outer_role, inner_role))
                    if outer_role == inner_role == 'explicit':
                        doubly_explicit_coordinates.append((_i, _j))
                format_cell_entries.append(inner_format_cell_entries)
            else:
                # Represent an entire inner list with an entry.
                format_cell_entries.append(outer_entry)
        
        # Where roles are 'explicit' outside and inside, we'll make 
        # surrounding roles be implicit for a more compact 
        # representation (avoiding redundant information).
        for (_i, _j) in doubly_explicit_coordinates:
            # Make implicit "above" (before w.r.t. outer level)
            _k = 1
            while True:
                expr, outer_role, inner_role = format_cell_entries[_i - _k][_j]
                format_cell_entries[_i - _k][_j] = (
                        expr, outer_role, 'implicit')
                if format_cell_entries[_i - _k][_j][1] == 0:
                    break # First of the ExprRange -- done.
                _k += 1
            # Make implicit "below" (after w.r.t. outer level)
            expr, outer_role, inner_role = format_cell_entries[_i + 1][_j]
            format_cell_entries[_i + 1][_j] = (expr, outer_role, 'implicit')
            # Make implicit to the "left" (before w.r.t. inner level).
            _k = 1
            while True:
                expr, outer_role, inner_role = format_cell_entries[_i][_j - _k]
                format_cell_entries[_i][_j - _k] = (
                        expr, 'implicit', inner_role)
                if format_cell_entries[_i][_j - _k][2] == 0: 
                    break # First of the ExprRange -- done.
                _k += 1
            # Make implicit to the "right" (after w.r.t. inner level).
            expr, outer_role, inner_role = format_cell_entries[_i][_j + 1]
            format_cell_entries[_i][_j + 1] = (expr, 'implicit', inner_role)
        
        return format_cell_entries

    def get_outer_format_cell_element_positions(self):
        '''
        Returns a list of element positions in correspondence with
        each row/column of this ExprArray/VertExprArray.  This 
        simply returns ExprTuple.get_format_cell_element_positions.

        The assumptions dictate simplifications that may apply to
        the element positions.
        '''
        return ExprTuple.get_format_cell_element_positions()

    def get_inner_format_cell_element_positions(self):
        '''
        Returns a list of element positions in correspondence with
        each column/row of this ExprArray/VertExprArray.  Raises
        a ValueError if these positions are not consistent among
        the different rows/columns of this ExprArray/VertExprArray.

        The assumptions dictate simplifications that may apply to
        the element positions.
        '''
        from proveit import ExprRange, VertExprArray
        element_positions = None
        for outer_entry in self.entries:
            if isinstance(outer_entry, ExprRange):
                outer_entry = outer_entry.body
            if isinstance(outer_entry, ExprTuple):
                cur_elem_positions = (
                        outer_entry.get_format_cell_element_positions())
                if element_positions is None:
                    element_positions = cur_elem_positions
                else:
                    if element_positions != cur_elem_positions:
                        if isinstance(self, VertExprArray):
                            raise ValueError(
                                    "Rows do not line up across different "
                                    "columns in VertExprArray: %s"%self)
                        else:
                            raise ValueError(
                                    "Columns do not line up across different "
                                    "rows in ExprArray: %s"%self)
        if element_positions is None:
            from proveit.numbers import one
            return [one] # only ExprRanges -- they start at qubit 1.
        return element_positions

    @staticmethod
    def vertical_explicit_cell_latex(expr_latex, nested_range_depth):
        '''
        Return the formatted cell, given the LaTeX of the 
        expression of the cell, with two vertical dots above and below 
        to denote an explicit parameterization of a vertical ExprRange.
        '''
        # Wrap with two vertical dots above and below.
        n = nested_range_depth
        return (r'\begin{array}{c}' + r':\\ '*n + expr_latex 
                + r' \\:'*n + '\end{array}')
    
    @staticmethod
    def horizontal_explicit_cell_latex(expr_latex, nested_range_depth):
        '''
        Return the formatted cell, given the LaTeX of the expression of 
        the cell, with two centered dots before and after to denote an 
        explicit parameterization of a horizontal ExprRange.
        '''
        # Wrap with two horizontal dots before and after.
        n = nested_range_depth
        return  (r'\cdot \cdot '*n + expr_latex + r' \cdot \cdot'*n)    
    
    def get_latex_formatted_cells(self, orientation='horizontal',
                                  vertical_explicit_cell_latex_fn=None,
                                  horizontal_explicit_cell_latex_fn=None,
                                  format_cell_entries=None,
                                  **cell_latex_kwargs):
        '''
        Return cells of this ExprArray formatted for LaTeX.
        
        The entries themselves may optionally be passed back via
        format_cell_entries (provide an empty list).
        
        The 'cell_latex_kwargs' will be passed as keyword arguments
        to the 'latex' calls for formatting each cell.
        '''
        from .vert_expr_array import VertExprArray
        # Depending upon the orientation, outer/inner ellipses
        # are vertical/horizontal dots.
        def vert_ellipses(nested_range_depth):
            n = nested_range_depth
            if n == 1: return r'\vdots'
            return (r'\begin{array}{c}' + r'\\ '.join([r'\vdots']*n)
                    + r'\end{array}')
        def horiz_ellipses(nested_range_depth):
            return r'\cdots'*nested_range_depth
        outer_ellipsis = (vert_ellipses if orientation=='horizontal'
                          else horiz_ellipses)
        inner_ellipsis = (horiz_ellipses if orientation=='horizontal'
                          else vert_ellipses)
        
        if vertical_explicit_cell_latex_fn is None:
            vertical_explicit_cell_latex_fn = (
                    ExprArray.vertical_explicit_cell_latex)
        if horizontal_explicit_cell_latex_fn is None:
            horizontal_explicit_cell_latex_fn = (
                    ExprArray.horizontal_explicit_cell_latex)
        def vertical_expr_to_latex(expr, **cell_latex_kwargs):
            # When formatting an ExprRange in a cell, show it as a
            # vertical array.
            if isinstance(expr, ExprRange):
                expr = VertExprArray([expr])
            return expr.latex(**cell_latex_kwargs)
        def horizonal_expr_to_latex(expr, **cell_latex_kwargs):
            # When formatting an ExprRange in a cell, show it as a
            # horizontal array.
            if isinstance(expr, ExprRange):
                expr = ExprArray([expr])
            return expr.latex(**cell_latex_kwargs)
        
        if orientation == 'horizontal':
            outer_explicit_formatted_cell, inner_explicit_formatted_cell = (
                    vertical_explicit_cell_latex_fn,
                    horizontal_explicit_cell_latex_fn)
            outer_expr_to_latex, inner_expr_to_latex = (
                    vertical_expr_to_latex, horizonal_expr_to_latex)
        elif orientation == 'vertical':
            outer_explicit_formatted_cell, inner_explicit_formatted_cell = (
                    horizontal_explicit_cell_latex_fn,
                    vertical_explicit_cell_latex_fn)
            outer_expr_to_latex, inner_expr_to_latex = (
                    horizonal_expr_to_latex, vertical_expr_to_latex)
        else:
            raise ValueError("'orientation' must be 'horizontal' or "
                             "'vertical', not %s"%orientation)
        
        formatted_cells = []
        format_cell_entries = self.get_format_cell_entries(format_cell_entries)
        for inner_format_cell_entries in format_cell_entries:
            if isinstance(inner_format_cell_entries, list):
                # Explicit inner list.
                inner_formatted_cells = []
                for entry in inner_format_cell_entries:
                    expr, outer_role, inner_role = entry
                    if isinstance(expr, ExprRange):
                        nested_range_depth = expr.nested_range_depth()
                    else:
                        nested_range_depth = 1
                    if outer_role == 'param_independent':
                        if inner_role == 'param_independent':
                            # Use diagonal dots it is parameter
                            # independent in both directions.
                            formatted_cell = r'\ddots'
                        else:
                            # Express a repetition of an outer range 
                            # where the body is parameter independent.
                            formatted_cell = outer_explicit_formatted_cell(
                                    outer_expr_to_latex(
                                            expr.formatted_repeats('latex')), 
                                    nested_range_depth)                        
                    elif outer_role == 'implicit':
                        if inner_role in ('implicit', 'explicit',
                                          'param_independent'):
                            # Use diagonal dots where the outer role
                            # is implicit and we are in the center of
                            # a range of tuples of ranges.
                            formatted_cell = r'\ddots'
                        else:
                            # Use vertical/horizontal dots where the
                            # outer role is 'implicit'.
                            formatted_cell = outer_ellipsis(nested_range_depth)
                    elif outer_role == 'explicit':
                        if inner_role in ('implicit', 'param_independent'):
                            # Use diagonal dots where the inner role
                            # is implicit and we are in the center of
                            # a range of tuples of ranges.
                            formatted_cell = r'\ddots'
                        elif inner_role == 'explicit':
                            # 'explicit' outer and inner role.  Format
                            # the body at the center of a range of
                            # tuples of ranges.
                            formatted_cell = expr.body.latex(
                                    **cell_latex_kwargs)
                        else:
                            formatted_cell = outer_explicit_formatted_cell(
                                    outer_expr_to_latex(expr.body), 
                                    nested_range_depth)
                    elif inner_role == 'param_independent':
                        # Express a repetition of an inner range 
                        # where the body is parameter independent.
                        formatted_cell = inner_explicit_formatted_cell(
                                expr.formatted_repeats('latex'), 
                                nested_range_depth)                     
                    elif inner_role == 'explicit':
                        formatted_cell = inner_explicit_formatted_cell(
                                inner_expr_to_latex(expr.body), 
                                nested_range_depth)
                    elif inner_role == 'implicit':
                        formatted_cell = inner_ellipsis(nested_range_depth)
                    else:
                        # default:
                        formatted_cell = expr.latex(**cell_latex_kwargs)
                    inner_formatted_cells.append(formatted_cell)                        
                formatted_cells.append(inner_formatted_cells)
            else:
                # The entire inner list is represented by one entry.
                expr, role = inner_format_cell_entries
                if isinstance(expr, ExprRange):
                    nested_range_depth = expr.nested_range_depth()
                else:
                    nested_range_depth = 1
                if role == 'param_independent':
                    # Express a repetition of an inner range 
                    # where the body is parameter independent.
                    formatted_cell = outer_explicit_formatted_cell(
                            expr.formatted_repeats('latex'), 
                            nested_range_depth)
                elif role == 'explicit' or role == 'param_independent':
                    formatted_cells.append(outer_explicit_formatted_cell(
                            outer_expr_to_latex(expr.body), 
                            nested_range_depth))
                elif role == 'implicit':
                    # Use vertical/horizontal dots
                    formatted_cells.append(
                            outer_ellipsis(nested_range_depth))
                else:
                    formatted_cells.append(expr.latex(**cell_latex_kwargs))
        return formatted_cells

    def latex(self, orientation='horizontal', fence=False, **kwargs):
        justification = self.get_style('justification', 'center')
        
        # Check that the columns are properly aligned by calculating
        # element positions of each column.
        self.get_inner_format_cell_element_positions()
        
        # Get latex-formatted cells.
        formatted_cells = self.get_latex_formatted_cells(
                orientation=orientation)
        
        # row', 'width' and 'height' nomenclature below is used for 
        # convenience assuming the orientation is 'horizontal' but the
        # roles will be switched if it is 'vertical'.
        height = len(formatted_cells)
        width = 1
        for formatted_row_entries in formatted_cells:
            if isinstance(formatted_row_entries, list):
                width = max(width, len(formatted_row_entries))
        
        if orientation == 'vertical':
            # Roles are now switched since the orientation is vertical.
            width, height = height, width

        out_str = ''
        if fence:
            out_str = r'\left('        
        out_str = r'\begin{array}{%s} ' % (
            justification[0] * width) + '\n '
        
        if orientation == 'horizontal':
            for formatted_row_entries in formatted_cells:
                if isinstance(formatted_row_entries, list):
                    if len(formatted_row_entries) > width:
                        # This row is short, so pad it.
                        formatted_row_entries.extend(
                                ['']*(width - len(formatted_row_entries)))
                    out_str += ' & '.join(formatted_row_entries)
                    out_str += r' \\' + '\n'
                else:
                    formatted_row = formatted_row_entries
                    out_str += r'\multicolumn{%d}{%s}{'%(width, 
                                                         justification[0])
                    out_str += (r'\begin{array}{lcr} \leftarrow & ' 
                                + formatted_row + r' & \rightarrow \end{array}} \\'
                                + '\n')
        elif orientation == 'vertical':
            for row in range(height):
                formatted_row_entries = []
                for col in range(width):
                    formatted_col_entries = formatted_cells[col]
                    if isinstance(formatted_col_entries, list):
                        formatted_row_entries.append(
                                formatted_col_entries[row])
                    elif row==0:
                        formatted_col = formatted_col_entries
                        formatted_row_entries.append(
                                r'\multirow{%d}{*}{$'%height +
                                (r'\begin{array}{c} \uparrow \\ %s \\ '
                                 %formatted_col) +
                                r'\downarrow \end{array}$}')
                    else:
                        formatted_row_entries.append('')
                out_str += ' & '.join(formatted_row_entries) 
                out_str += r' \\' + '\n'
            
        else:
            raise ValueError("'orientation' must be 'horizontal' or "
                             " 'vertical', not %s"%orientation)
        
        out_str += r'\end{array}' + '\n'
        if fence:
            out_str = r'\right)'
        return out_str

    def num_elements(self, **defaults_config):
        '''
        Return the proven number of elements of this ExprArray as an 
        ExprTuple.  This includes the extent of all contained ranges.
        '''
        from proveit.core_expr_types import Len
        return Len(self[:]).computed(**defaults_config)