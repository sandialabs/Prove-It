from .expr_tuple import ExprTuple
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_.defaults import USE_DEFAULTS


class ExprArray(ExprTuple):
    '''
    An ExprArray is simply an ExprTuple of ExprTuples or ExprRanges.
    The array is broken up into different rows after each ExprTuple
    or ExprRange. Each column MUST contain the same type of expression.
    '''

    def __init__(self, *expressions, styles=None):
        '''
        Initialize an ExprArray from an iterable over ExprTuple
        objects or Expressions that represent ExprTuples.
        '''
        ExprTuple.__init__(self, *expressions, styles=styles)

    @classmethod
    def _make(sub_class, core_info, sub_expressions, *, styles):
        if sub_class != ExprArray:
            MakeNotImplemented(sub_class)
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
    
    def get_format_cell_entries(self):
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
        '''
        
        # TODO: Check alignment 'implicit'/'explicit' cells, making
        # sure they represent the same number of elements.
        
        # Construct the list of (for the most part) lists of entries
        # first by simply composing outer and inner roles.
        # Remember coordinates of entries that are 'explicit' outside
        # and inside -- we'll edit their surrounding entries next.
        format_cell_entries = []
        doubly_explicit_coordinates = []
        for _i, outer_entry in enumerate(
                ExprTuple.get_format_cell_entries(self)):
            outer_expr, outer_role = outer_entry
            if isinstance(outer_expr, ExprTuple):
                # An explicit inner list.
                inner_format_cell_entries = []
                for _j, inner_entry in enumerate(
                        outer_expr.get_format_cell_entries()):
                    inner_expr, inner_role = inner_entry
                    # Compose outer and inner roles.
                    inner_format_cell_entries.append(
                            (inner_expr, outer_role, inner_role))
                    if outer_role == inner_role == 'explicit':
                        doubly_explicit_coordinates.append((_i, _j))
                format_cell_entries.append(inner_format_cell_entries)
            else:
                # Represent an entire inner list with an entry.
                format_cell_entries.append((outer_expr, outer_role))
        
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

    def get_outer_format_cell_element_positions(self, assumptions=USE_DEFAULTS,
                                         _remembered_simplifications=None):
        '''
        Returns a list of element positions in correspondence with
        each row/column of this ExprArray/VertExprArray.  This 
        simply returns ExprTuple.get_format_cell_element_positions.

        The assumptions dictate simplifications that may apply to
        the element positions.
        '''
        return ExprTuple.get_format_cell_element_positions(
                assumptions, _remembered_simplifications)

    def get_inner_format_cell_element_positions(
            self, assumptions=USE_DEFAULTS, _remembered_simplifications=None):
        '''
        Returns a list of element positions in correspondence with
        each column/row of this ExprArray/VertExprArray.  Raises
        a ValueError if these positions are not consistent among
        the different rows/columns of this ExprArray/VertExprArray.

        The assumptions dictate simplifications that may apply to
        the element positions.
        '''
        from proveit import ExprRange, VertExprArray
        if _remembered_simplifications is None:
            _remembered_simplifications = dict()
        element_positions = None
        for outer_entry in self.entries:
            if isinstance(outer_entry, ExprRange):
                outer_entry = outer_entry.body
            if isinstance(outer_entry, ExprTuple):
                cur_elem_positions = (
                        outer_entry.get_format_cell_element_positions(
                                assumptions, _remembered_simplifications))
                if element_positions is None:
                    element_positions = cur_elem_positions
                else:
                    if element_positions != cur_elem_positions:
                        if isinstance(self, VertExprArray):
                            raise ValueError(
                                    "Rwos do not line up across different "
                                    "columns in VertExprArray: %s"%self)
                        else:
                            raise ValueError(
                                    "Columns do not line up across different "
                                    "rows in ExprArray: %s"%self)
        return element_positions

    
    def get_latex_formatted_cells(self, orientation='horizontal'):
        '''
        Return cells of this ExprArray formatted for LaTeX.
        '''
        # Depending upon the orientation, outer/inner ellipses
        # are vertical/horizontal dots.
        outer_ellipsis = (r'\vdots' if orientation=='horizontal'
                          else r'\cdots')
        inner_ellipsis = (r'\cdots' if orientation=='horizontal'
                          else r'\vdots')
        # These function will switch if the orientation is 'vertical'.
        def outer_explicit_formatted_cell(expr):
            # Wrap with two vertical dots above and below.
            return r'\begin{array}{c}:\\ %s \\:\end{array}'%expr.latex()
        def inner_explicit_formatted_cell(expr):
            # Wrap with two horizontal dots before and after.
            return  r'\cdot \cdot ' + expr.latex() + r' \cdot \cdot'
        # Switch if the  orientation is 'vertical':
        if orientation != 'horizontal':
            if orientation != 'vertical':
                raise ValueError("'orientation' must be 'horizontal' or "
                                 "'vertical', not %s"%orientation)
            inner_explicit_formatted_cell, outer_explicit_formatted_cell = (
                outer_explicit_formatted_cell, inner_explicit_formatted_cell)
        
        formatted_cells = []
        format_cell_entries = self.get_format_cell_entries()
        for inner_format_cell_entries in format_cell_entries:
            if isinstance(inner_format_cell_entries, list):
                # Explicit inner list.
                inner_formatted_cells = []
                for entry in inner_format_cell_entries:
                    expr, outer_role, inner_role = entry
                    if outer_role == 'implicit':
                        if inner_role in ('implicit', 'explicit'):
                            # Use diagonal dots where the outer role
                            # is implicit and we are in the center of
                            # a range of tuples of ranges.
                            formatted_cell = r'\ddots'
                        else:
                            # Use vertical/horizontal dots where the
                            # outer role is 'implicit'.
                            formatted_cell = outer_ellipsis
                    elif outer_role == 'explicit':
                        if inner_role == 'implicit':
                            # Use diagonal dots where the inner role
                            # is implicit and we are in the center of
                            # a range of tuples of ranges.
                            formatted_cell = r'\ddots'
                        elif inner_role == 'explicit':
                            # 'explicit' outer and inner role.  Format
                            # the body at the center of a range of
                            # tuples of ranges.
                            formatted_cell = expr.latex()
                        else:
                            formatted_cell = outer_explicit_formatted_cell(
                                    expr)
                    elif inner_role == 'implicit':
                        formatted_cell = inner_ellipsis
                    elif inner_role == 'explicit':
                        formatted_cell = inner_explicit_formatted_cell(expr)
                    else:
                        formatted_cell = expr.latex() # default
                    inner_formatted_cells.append(formatted_cell)                        
                formatted_cells.append(inner_formatted_cells)
            else:
                # The entire inner list is represented by one entry.
                expr, role = inner_format_cell_entries
                if role == 'implicit':
                    # Use vertical/horizontal dots
                    formatted_cells.append(outer_ellipsis)
                elif role == 'explicit':
                    formatted_cells.append(outer_explicit_formatted_cell(
                            outer_ellipsis))
                else:
                    formatted_cells.append(expr.latex())
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
        width = 0
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
            out_str = r'\right('
        return out_str
        