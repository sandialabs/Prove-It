from proveit import (Expression, Function, Literal, 
                     ExprArray, VertExprArray, StyleOptions)
from proveit.logic import Set
from proveit.physics.quantum.circuits.qcircuit_elements import (
        Gate, MultiQuditGate, Input, Output)

class Qcircuit(Function):
    '''
    A quantum circuit represented in column-major order.
    '''
    
    DEFAULT_SPACING = '@C=1em @R=.7em'

    # the literal operator of the Qcircuit operation class
    _operator_ = Literal('QCIRCUIT', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        '''
        Initialize a Qcircuit from either or VertExprArray or
        columns to generate a VertExprArray.
        '''
        if len(operands)==1 and isinstance(operands[0], VertExprArray):
            vert_expr_array = operands[0]
        else:
            vert_expr_array = VertExprArray(*operands)
        Function.__init__(self, Qcircuit._operator_,
                          vert_expr_array, styles=styles)
        self.vert_expr_array = vert_expr_array

    def style_options(self):
        '''
        Return the StyleOptions object for this Circuit.
        '''
        options = StyleOptions(self)
        options.add_option(
            name = 'spacing',
            description = (
                    "change the spacing of a circuit using the format "
                    "'@C=1em @R=.7em' where C is the column spacing and "\
                    "R is the row spacing"),
            default = Qcircuit.DEFAULT_SPACING,
            related_methods = ())
        return options

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        call_strs = []
        spacing = self.get_style('spacing')
        if spacing != Qcircuit.DEFAULT_SPACING:
            call_strs.append('with_style(spacing="' + spacing + '")')
        return call_strs

        
    def _config_latex_tool(self, lt):
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')
    
    @staticmethod
    def _find_down_wire_locations(format_cell_entries,
                                  format_row_element_positions):
        '''
        Return the set of (row, col) locations of the circuit
        grid where we should have a vertical wire to the next row.
        We will raise an exception if there are rowset inconsistencies
        among MultiQuditGate entries.
        '''
        down_wire_locations = set()
        position_set_to_python_set = dict()
        
        # Iterate over each column.
        for col, col_entries in enumerate(format_cell_entries):
            if isinstance(col_entries, Expression):
                # An Expression represents the entire column.
                # There are no multi-qubit gates to worry about.
                continue
            assert isinstance(col_entries, list)
            
            # Iterate over each row. Map qudit position sets of
            # MultiQuditGates sets of rows that may be involved. 
            qudit_positions_to_rows = dict()
            for row, entry in enumerate(col_entries):
                entry = entry[0] # the actual Expression of the entry
                qudit_position = format_row_element_positions[row]
                if isinstance(entry, MultiQuditGate):
                    # MultiQuditGate entry.
                    qudit_positions = entry.qudit_positions
                    if isinstance(qudit_positions, Set):
                        # MultiQuditGate entry has an explicit Set of
                        # qudit_positions.
                        # Remember this Set as a python set so we
                        # can check membership efficiently.
                        if qudit_positions in position_set_to_python_set:
                            python_set = position_set_to_python_set[
                                    qudit_positions]
                        else:
                            python_set = set(qudit_positions.operands)
                            position_set_to_python_set[qudit_positions] = (
                                    python_set)
                        if qudit_position not in python_set:
                            # Uh-oh, the current qudit_position is not
                            # contained in the explicit set of qudit
                            # positions.
                            raise ValueError(
                                    "%s not explicitly contained in "
                                    "%s.  The Qcircuit may have an error "
                                    "or qudit positions may not be "
                                    "simplifying in a consistent manner.")
                    # Mark this format row as one corresponding with
                    # the qudit_positions of the MultiQuditGate.
                    qudit_positions_to_rows.setdefault(
                            qudit_positions, set()).add(row)
            # For each set of qudit positions, record the last 
            # corresponding format row.  Also, make sure all qudit
            # positions of MultiQuditGates are accounted for with each
            # MultiQuditGate that has explicit qudit positions in the
            # column.
            qudit_positions_to_maxrow = dict()
            for qudit_positions, rows in qudit_positions_to_rows.items():
                if isinstance(qudit_positions, Set):
                    num_qudit_positions = len(set(qudit_positions.operands))
                    if num_qudit_positions != len(rows):
                        # We checked each row as they came along, so
                        # there must be more qudit_positions if the
                        # counts differ:
                        assert num_qudit_positions > len(row)
                        raise ValueError(
                                "There are only %d MultiQudit gates having "
                                "the %d qudit positions of %s in column %d."
                                %(len(row), num_qudit_positions, 
                                  qudit_positions, col))
                qudit_positions_to_maxrow[qudit_positions] = max(rows)
            
            # Now we can add 'down wire' locations appropriately for
            # this column.
            for row, entry in enumerate(col_entries):
                entry = entry[0] # the actual Expression of the entry
                if isinstance(entry, MultiQuditGate):
                    qudit_positions = entry.qudit_positions
                    if row < qudit_positions_to_maxrow[qudit_positions]:
                        # Add a wire down from this location since it
                        # is not the last row of the MultiQuditGate
                        # qudit positions.
                        down_wire_locations.add((row, col))
        
        # Return all 'down wire' location.
        return down_wire_locations

    def latex(self, fence=False, **kwargs):
        spacing = self.get_style('spacing')
            
        # Get the element positions corresponding to each row of the
        # array, raising a ValueError if there are inconsistencies.
        vert_expr_array = self.vert_expr_array
        format_row_element_positions = (
                vert_expr_array.get_format_row_element_positions())
        
        # When we have an explicit parameterization of a
        # horizontal or vertical ExprArray, we put two dots before&after
        # or above&below.  If this is for a gate, input, or output,
        # we should wrap the gate/lstick/rstick around these dots.
        def inside_gate_wrapper(explicit_cell_latex_fn):
            def new_explicit_cell_latex_fn(expr_latex):
                if expr_latex[:6] == r'\gate{' and  expr_latex[-1]=='}':
                    return r'\gate{%s}'%explicit_cell_latex_fn(expr_latex[6:-1])
                elif expr_latex[:8] == r'\lstick{' and  expr_latex[-1]=='}':
                    return r'\lstick{%s}'%explicit_cell_latex_fn(
                            expr_latex[8:-1])
                elif expr_latex[:8] == r'\rstick{' and  expr_latex[-1]=='}':
                    return r'\rstick{%s}'%explicit_cell_latex_fn(
                            expr_latex[8:-1])
            return new_explicit_cell_latex_fn
        
        # Get latex-formatted cells.  Indicate that these should be
        # formatted in the context of being within a Qcircuit
        format_cell_entries = []
        formatted_cells = vert_expr_array.get_latex_formatted_cells(
                format_cell_entries=format_cell_entries,
                vertical_explicit_cell_latex_fn=inside_gate_wrapper(
                        ExprArray.vertical_explicit_cell_latex),
                horizontal_explicit_cell_latex_fn=inside_gate_wrapper(
                        ExprArray.horizontal_explicit_cell_latex),
                within_qcircuit=True)
        
        width = len(formatted_cells)
        height = 0
        for formatted_col_entries in formatted_cells:
            if isinstance(formatted_col_entries, list):
                height = max(height, len(formatted_col_entries))
        
        out_str = ''
        if fence:
            out_str = r'\left('
        out_str += r'\hspace{2em} \Qcircuit' + spacing + '{' + '\n'
        
        # Find locations where we should add a downward wire.
        down_wire_locations = Qcircuit._find_down_wire_locations(
                format_cell_entries, format_row_element_positions)
        for row in range(height):
            formatted_row_entries = []
            for col in range(width):
                format_col_entries = format_cell_entries[col]
                formatted_col_entries = formatted_cells[col]
                # MUST FIGURE OUT WHAT TO DO WITH outer_explicit_formatted_cell and inner_explicit_formatted_cell: TODO
                if isinstance(formatted_col_entries, list):
                    formatted_entry = formatted_col_entries[row]
                    entry = format_col_entries[row][0]
                    if formatted_entry in (r'\cdots', r'\vdots', r'\ddots'):
                        # Wrap ellipses in \gate, \lstick, or \rstick
                        # as appropriate.
                        if (isinstance(entry, Gate) or 
                                isinstance(entry, MultiQuditGate)):
                            formatted_entry = r'\gate{%s}'%formatted_entry
                        elif isinstance(entry, Input):
                            formatted_entry = r'\lstick{%s}'%formatted_entry
                        elif isinstance(entry, Output):
                            formatted_entry = r'\rstick{%s}'%formatted_entry
                    if isinstance(entry, MultiQuditGate):
                        if entry.get_style('representation') == 'block':
                            assert formatted_entry[:5] == r'\gate'
                            if (row-1, col) not in down_wire_locations:
                                # Add up the length of the block.
                                _bl = 0
                                while (entry==format_col_entries[row+_bl]):
                                    _bl += 1
                                # The top-most of a block gate.
                                formatted_entry = (
                                        r'\multigate{%d}'%_bl +
                                        formatted_entry[5:])
                            else:
                                # Not the top-most of a block gate,
                                # so we must use 'ghost'.
                                formatted_entry = (
                                        r'\ghost' + formatted_entry[5:])
                    if (row, col) in down_wire_locations:
                        formatted_entry += r' \qwx[1]'                                
                    formatted_row_entries.append(formatted_entry)
                else:
                    # Use up and down arrows above and below to denote 
                    # an expression representing an entire column.
                    formatted_col = (r'\begin{array}{c} \uparrow \\'
                                     '%s \\ \downarrow\end{array}'
                                     %formatted_col_entries)
                    if row==0:
                        # An expression represents the entire row: top
                        formatted_row_entries.append(
                                r'\multigate{%d}{%s}'%(height, formatted_col))
                    else:
                        # An expression represents the entire row: not top
                        formatted_col = formatted_col_entries
                        formatted_row_entries.append(r'\ghost{%s}'%formatted_col)
            out_str += '& ' + ' & '.join(formatted_row_entries) 
            if row != height-1:
                out_str += r' \\' + '\n'
        
        out_str += ' \n' + r'} \hspace{2em}'
        if fence:
            out_str = r'\right)'
        return out_str

    """
    def replace_equiv_circ(self, current, new, assumptions=USE_DEFAULTS):
        '''
        Given the piece that is to be replaced, and the piece it is being replaced with,
        use either space_equiv or time_equiv to prove the replacement.
        '''
        from . import sing_time_equiv, time_equiv, sing_space_equiv, two_qubit_space_equiv
        if not isinstance(current, Circuit):
            raise ValueError(
                'The current circuit piece must be a circuit element.')
        if not isinstance(new, Circuit):
            raise ValueError(
                'The replacement piece must be a circuit element.')
        if current.get_col_height() != new.get_col_height(
        ) or current.get_row_length() != new.get_row_length():
            raise ValueError(
                'The current circuit element and the replacement circuit element must be the same size.')
        if current.get_row_length() == 1 and current.get_col_height() == self.get_col_height():
            # return sing_time_equiv.instantiate({h:l, k:l, m: self.get_col_height, n:l, A:l, B: current, C:l, D: new, R:l, S: , Q:l},
            #           assumptions=assumptions)
            pass
    """