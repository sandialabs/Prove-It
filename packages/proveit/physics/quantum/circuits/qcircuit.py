from proveit import (Expression, Function, Literal, 
                     ConditionalSet, Conditional,
                     ExprTuple, ExprArray, VertExprArray, StyleOptions)
from proveit.logic import Set
from proveit.physics.quantum.circuits.qcircuit_elements import (
        Gate, MultiQuditGate, Ghost, Input, Output)

class Qcircuit(Function):
    '''
    A quantum circuit represented in column-major order.
    '''
    
    DEFAULT_SPACING = '@C=1em @R=.7em'

    # the literal operator of the Qcircuit operation class
    _operator_ = Literal('QCIRCUIT', theory=__file__)
    
    def __init__(self, vert_expr_array, *, styles=None):
        '''
        Initialize a Qcircuit from either or VertExprArray or
        columns to generate a VertExprArray.
        '''
        Function.__init__(self, Qcircuit._operator_,
                          vert_expr_array, styles=styles)
        self.vert_expr_array = vert_expr_array
    
    @classmethod
    def extract_init_arg_value(cls, arg_name, operator, operands):
        if arg_name == 'vert_expr_array':
            return operands

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
        We also check for MultiQuditGate consistencies, raising
        ValueError or TypeError if there is an inconsistency.
        '''
        from proveit.physics.quantum import (
                CONTROL, CLASSICAL_CONTROL, SWAP)
        down_wire_locations = set()
        qudit_position_to_row = {pos:row for row, pos in 
                                 enumerate(format_row_element_positions)}
        
        # Iterate over each column.
        for col, col_entries in enumerate(format_cell_entries):
            if isinstance(col_entries, Expression):
                # An Expression represents the entire column.
                # There are no multi-qubit gates to worry about.
                continue
            assert isinstance(col_entries, list)
            
            # Iterate over each row. Map qudit position sets of
            # MultiQuditGates sets of rows that may be involved. 
            qudit_positions_of_column = set()
            # No vertical wire through multigate (blockade):
            multigate_blockade = set() 
            has_generic_multiquditgate = False
            for row, entry in enumerate(col_entries):
                entry = entry[0] # the actual Expression of the entry
                qudit_position = format_row_element_positions[row]
                if isinstance(entry, MultiQuditGate):
                    # MultiQuditGate entry.
                    gate_op = entry.gate_operation
                    qudit_positions = entry.qudit_positions
                    qudit_positions_of_column.add(qudit_positions)
                    is_multi_gate = False
                    if isinstance(qudit_positions, Set):
                        # Explicit qudit positions for a control or
                        # swap operation (order doesn't matter).
                        if gate_op not in (CONTROL, CLASSICAL_CONTROL, SWAP):
                            raise ValueError(
                                    "For a multi-gate, %s, use an ExprTuple "
                                    "for the qudit_positions rather than "
                                    "a Set (order matters)."%str(gate_op))
                        qudit_positions = qudit_positions.operands                        
                    elif isinstance(qudit_positions, ExprTuple):
                        # Explicit qudit positions for a multi-gate
                        # (order does matter)
                        if gate_op in (CONTROL, CLASSICAL_CONTROL, SWAP):
                            raise ValueError(
                                    "For MultiQuditGates %s operations; "
                                    "use a Set for the qudit_positions "
                                    "rather than ExprTuple (order does "
                                    "not matter)."%gate_op)
                        is_multi_gate = True
                    else:
                        # A "generic" MultiQuditGate (no explicit
                        # qudit_positions).
                        has_generic_multiquditgate = True

                    if qudit_positions.contains_range():
                        raise ValueError(
                                "Explicit qudit positions "
                                "should not contain an ExprRange.")
                    
                    if is_multi_gate:
                        # A multi-gate.  The qudit_positions must
                        # be consecutive and all entries beyond the
                        # top must be proper "Ghost" entries.
                        for _k, multigate_position in enumerate(
                                qudit_positions):
                            next_position = (
                                    format_row_element_positions[row+_k])
                            if (next_position != multigate_position):
                                raise ValueError(
                                        "Multi-gate qudit positions "
                                        "must match consecutive rows: "
                                        "%s ≠ %s."
                                        %(multigate_position,
                                          next_position))
                            if _k > 0:
                                multigate_blockade.add(row+_k-1)
                                entry_below = col_entries[row+_k][0]
                                if not isinstance(entry_below, Ghost):
                                    raise TypeError(
                                            "Entry below a multi-gate for "
                                            "%s operation expected to be "
                                            "a Ghost, but got %s"
                                            %(entry.gate_operation, 
                                              entry_below))
                                if (entry_below.gate_operation != 
                                        entry.gate_operation):
                                    raise TypeError(
                                            "Entry below a multi-gate for "
                                            "%s operation expected to be "
                                            "a Ghost for this operation, "
                                            "not for %s."
                                            %(entry.gate_operation, 
                                              entry_below.gate_operation))
                    else:
                        # For a control or a swap, make sure the 
                        # qudit_positions all exist and have 
                        # appropriate entries.

                        # If it is a SWAP, it involve two qudits.
                        if (gate_op == SWAP and 
                                qudit_positions.num_entries() != 2):
                            raise ValueError(
                                    "For a SWAP, please use "
                                    "two qudit_positions, not %d"
                                    %qudit_positions.num_entries())
                        
                        # Other cases (e.g., a control with many
                        # targets), should have 
                        contains_cur_pos = False
                        for _other_pos in qudit_positions:
                            if _other_pos == qudit_position:
                                # The current position is contained.
                                contains_cur_pos = True
                                continue
                            if _other_pos not in qudit_position_to_row:
                                raise ValueError(
                                        "The qudit position of %s for a "
                                        "%s MultiQuditGate is not a known "
                                        "qudit_position of the Qcircuit, "
                                        "it is not in %s"
                                        %(_other_pos, gate_op,
                                          qudit_position_to_row.keys()))
                            _other_row = qudit_position_to_row[_other_pos]
                            _other_entry = col_entries[_other_row][0]
                            if gate_op == SWAP:
                                if _other_entry != entry:
                                    raise ValueError(
                                            "For a SWAP, please use "
                                            "two MultiQuditGates that are "
                                            "the same: %s ≠ %s."
                                            %(_other_entry, entry))
                            elif isinstance(_other_entry, Ghost):
                                raise ValueError(
                                        "A %s MultiQuditGate should not "
                                        "target part of a mult-gate except "
                                        "the top.")
                            elif (qudit_positions.num_entries() == 2 and
                                  gate_op == CONTROL and
                                  _other_entry.gate_operation == CONTROL):
                                # This a symmetrically-formed 
                                # controlled-Z (control on both ends).
                                # That's okay.
                                continue
                            if not (isinstance(_other_entry, Gate) or
                                    (isinstance(_other_entry, MultiQuditGate)
                                    and isinstance(_other_entry.qudit_positions,
                                                   ExprTuple))):
                                raise ValueError(
                                        "With exception to a symmetrically "
                                        "formed controlled-Z, the target "
                                        "of a control must be a gate or "
                                        "a multi-gate, not %s."
                                        %_other_entry)
                        if not contains_cur_pos:
                            raise ValueError(
                                    "The qudit positions of a MultiQuditGate "
                                    "must contain that of the MultiQuditGate "
                                    "itself, but %s is not in %s"
                                    %(qudit_position, qudit_positions))
            
            if has_generic_multiquditgate:
                # If there is a generic MultiQuditGate, we need
                # a vertical wire from top to bottom since anything
                # could be the target.
                for row, _ in enumerate(col_entries):
                    down_wire_locations.add((row, col))
            else:
                # Map minimum rows of qudit_positions to the
                # maximum of maximum rows of qudit_positions.
                minrow_to_maxrow = dict()
                qudit_positions_to_maxrow = dict()
                for qudit_positions in qudit_positions_of_column:
                    if isinstance(qudit_positions, Set):
                        positions_as_tuple = qudit_positions.operands
                    else:
                        positions_as_tuple = qudit_positions
                    assert isinstance(positions_as_tuple, ExprTuple)
                    pos_rows = [qudit_position_to_row[qudit_position] for
                                qudit_position in positions_as_tuple.entries]
                    maxrow = max(pos_rows)
                    minrow = min(pos_rows)
                    minrow_to_maxrow[minrow] = max(
                        minrow_to_maxrow.get(minrow, 0), maxrow)
                
                # Now we can add 'down wire' locations appropriately 
                # for this column.
                add_down_wires_to_row = 0
                for row, entry in enumerate(col_entries):
                    entry = entry[0] # the actual Expression of the 
                    if row in minrow_to_maxrow:
                        maxrow = minrow_to_maxrow[row]
                        add_down_wires_to_row = max(
                                add_down_wires_to_row, maxrow)
                    if (row < add_down_wires_to_row 
                            and row not in multigate_blockade):
                        # Add a wire down from this location since it 
                        # is before the last row of MultiQuditGate
                        # qudit positions, and it isn't blocked by a
                        # multigate.
                        down_wire_locations.add((row, col))
        
        # Return all 'down wire' location.
        return down_wire_locations

    def latex(self, fence=False, **kwargs):
        from proveit.physics.quantum import (
                CONTROL, CLASSICAL_CONTROL, SWAP)
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
                        _entry = entry
                        # If the entry is a conditional set, use the
                        # value of any of the conditionals to determine
                        # the type.
                        while (isinstance(_entry, ConditionalSet) or
                               isinstance(_entry, Conditional)):
                            if isinstance(_entry, ConditionalSet):
                                _entry = _entry.conditionals[0]
                            if isinstance(_entry, Conditional):
                                _entry = _entry.value
                        if (isinstance(_entry, Gate) or 
                                isinstance(_entry, MultiQuditGate)):
                            formatted_entry = r'\gate{%s}'%formatted_entry
                        elif isinstance(_entry, Input):
                            formatted_entry = r'\lstick{%s}'%formatted_entry
                        elif isinstance(_entry, Output):
                            formatted_entry = r'\rstick{%s}'%formatted_entry
                    if isinstance(entry, MultiQuditGate):
                        if isinstance(entry.qudit_positions, ExprTuple):
                            gate_op = entry.gate_operation
                            assert gate_op not in (
                                    CONTROL, CLASSICAL_CONTROL, SWAP)
                            # The top of a multi-gate (not a 
                            # control or swap and has explicit 
                            # qudit positions).
                            qudit_positions = entry.qudit_positions
                            if qudit_positions.contains_range():
                                raise ValueError(
                                        "Explicit qudit positions "
                                        "should not contain an "
                                        "ExprRange.")
                            nqdits = entry.qudit_positions.num_entries()
                            assert formatted_entry[:5] == r'\gate'
                            # The top-most of a block gate.
                            formatted_entry = (
                                    r'\multigate{%d}'%(nqdits-1) +
                                    formatted_entry[5:])
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
            out_str += r'\right)'
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
