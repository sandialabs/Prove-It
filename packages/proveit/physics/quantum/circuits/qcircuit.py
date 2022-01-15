from proveit import (Expression, Function, Literal, 
                     ConditionalSet, Conditional, ExprRange,
                     ExprTuple, ExprArray, VertExprArray, StyleOptions,
                     free_vars)
from proveit.logic import Set
from proveit.physics.quantum.circuits.qcircuit_elements import (
        Gate, MultiQubitElem, Input, Output, Measure, config_latex_tool)

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
        config_latex_tool(lt)
    
    @staticmethod
    def _find_down_wire_locations(format_cell_entries,
                                  format_row_element_positions):
        '''
        Return the set of (row, col) locations of the circuit
        grid where we should have a vertical wire to the next row.
        We also check for MultiQubitElem consistencies, raising
        ValueError or TypeError if there is an inconsistency.
        '''
        from proveit.physics.quantum import (
                CONTROL, CLASSICAL_CONTROL, SWAP)
        down_wire_locations = set()
        qubit_position_to_row = {pos:row for row, pos in 
                                 enumerate(format_row_element_positions)}
        
        # Iterate over each column.
        for col, col_entries in enumerate(format_cell_entries):
            if not isinstance(col_entries, list):
                # An Expression represents the entire column.
                # There are no multi-qubit gates to worry about.
                continue
            
            # Iterate over each row. Map qubit position sets of
            # MultiQubitElems sets of rows that may be involved. 
            qubit_positions_of_column = set()
            # No vertical wire through multigate (blockade):
            multigate_blockade = set() 
            has_generic_multiqubitelem = False
            active_multigate = None
            for row, entry in enumerate(col_entries):
                entry_expr = entry[0] # the actual Expression of the entry
                qubit_pos = format_row_element_positions[row]
                if isinstance(entry_expr, MultiQubitElem):
                    # MultiQubitElem entry.
                    elem = entry_expr.element
                    qubit_positions = entry_expr.qubit_positions
                    qubit_positions_of_column.add(qubit_positions)
                    is_multi_gate = False
                    is_generic_gate = False
                    if isinstance(qubit_positions, Set):
                        # Explicit qubit positions for a control or
                        # swap operation (order doesn't matter).
                        if elem not in (CONTROL, CLASSICAL_CONTROL, SWAP):
                            raise ValueError(
                                    "For a multi-gate, %s, use an ExprTuple "
                                    "for the qubit_positions rather than "
                                    "a Set (order matters)."%str(elem))
                        qubit_positions = qubit_positions.operands                        
                        if qubit_positions.contains_range():
                            raise ValueError(
                                    "Explicit qubit positions "
                                    "should not contain an ExprRange.")
                    elif isinstance(qubit_positions, ExprTuple):
                        # Explicit qubit positions for a multi-gate
                        # (order does matter)
                        if elem in (CONTROL, CLASSICAL_CONTROL, SWAP):
                            raise ValueError(
                                    "For MultiQubitElems %s operations; "
                                    "use a Set for the qubit_positions "
                                    "rather than ExprTuple (order does "
                                    "not matter)."%elem)
                        is_multi_gate = True
                    else:
                        # A "generic" MultiQubitElem (no explicit
                        # qubit_positions).
                        is_generic_gate = True
                        has_generic_multiqubitelem = True
                        
                    if is_multi_gate:
                        # A multi-gate.  The qubit_positions must
                        # be an ExprTuple of an ExprRange covering
                        # all of the involved qubits and each entry
                        # must be the same MultiQubitElem expression.
                        if (qubit_positions.num_entries() != 1 or
                                not isinstance(qubit_positions[0], ExprRange)):
                            raise ValueError(
                                    "To format a multigate in a Qcircuit, the " 
                                    "qubit_positions must be an ExprTuple "
                                    "with a single ExprRange, not %s"
                                    %qubit_positions)
                        qubit_positions_range = qubit_positions[0]
                        if (qubit_positions_range.body !=
                                qubit_positions_range.parameter):
                            raise ValueError(
                                    "To format a multigate in a Qcircuit, the " 
                                    "qubit_positions must be an ExprTuple "
                                    "with a single, simple ExprRange, not %s"
                                    %qubit_positions)
                        if active_multigate is None:
                            start_index = qubit_positions_range.start_index
                            if qubit_pos != start_index:
                                raise ValueError(
                                        "Mismatch of starting qubit position "
                                        "of a multigate: %s ≠ %s"
                                        %(qubit_pos, start_index))
                            active_multigate = entry_expr
                        else:
                            if entry_expr != active_multigate:
                                raise ValueError(
                                        "The MultiQubitElem expressions "
                                        "composing a multigate must be the "
                                        "same: %s %s"%(entry_expr,
                                                       active_multigate))
                            if qubit_pos == qubit_positions_range.end_index:
                                active_multigate = None
                        if active_multigate is not None:
                            # There is a continuing multigate, so block
                            # any down wire from this row.
                            multigate_blockade.add(row)
                    elif active_multigate is not None:
                        raise ValueError(
                                "The MultiQubitElem expressions "
                                "composing a multigate must be consecutive "
                                "up until the end qubit positions: "
                                "encountered %s before end of %s"
                                %(entry_expr, active_multigate))
                    elif not is_generic_gate:
                        # For a control or a swap, make sure the 
                        # qubit_positions all exist and have 
                        # appropriate entries.

                        # If it is a SWAP, it involve two qubits.
                        if (elem == SWAP and 
                                qubit_positions.num_entries() != 2):
                            raise ValueError(
                                    "For a SWAP, please use "
                                    "two qubit_positions, not %d"
                                    %qubit_positions.num_entries())
                        
                        # Other cases (e.g., a control with many
                        # targets), should have 
                        contains_cur_pos = False
                        for _other_pos in qubit_positions:
                            if _other_pos == qubit_pos:
                                # The current position is contained.
                                contains_cur_pos = True
                                continue
                            if _other_pos not in qubit_position_to_row:
                                raise ValueError(
                                        "The qubit position of %s for a "
                                        "%s MultiQubitElem is not a known "
                                        "qubit_position of the Qcircuit, "
                                        "it is not in %s"
                                        %(_other_pos, elem,
                                          qubit_position_to_row.keys()))
                            _other_row = qubit_position_to_row[_other_pos]
                            _other_entry_expr = col_entries[_other_row][0]
                            if elem == SWAP:
                                if _other_entry_expr != entry_expr:
                                    raise ValueError(
                                            "For a SWAP, please use "
                                            "two MultiQubitElems that are "
                                            "the same: %s ≠ %s."
                                            %(_other_entry_expr, entry_expr))
                            if isinstance(_other_entry_expr, MultiQubitElem):
                                other_qpositions = (
                                        _other_entry_expr.qubit_positions)
                                if (isinstance(other_qpositions, ExprTuple) and
                                        other_qpositions.num_entries() == 1 and
                                        isinstance(other_qpositions[0], 
                                                   ExprRange)):
                                    if (other_qpositions[0].start_index
                                            != _other_pos):
                                        raise ValueError(
                                                "A %s MultiQubitElem should "
                                                "not target part of a "
                                                "mult-gate except the top.")
                            elif (qubit_positions.num_entries() == 2 and
                                  elem == CONTROL and
                                  _other_entry_expr == CONTROL):
                                # This a symmetrically-formed 
                                # controlled-Z (control on both ends).
                                # That's okay.
                                continue
                            if not (isinstance(_other_entry_expr, Gate) or
                                    (isinstance(_other_entry_expr, MultiQubitElem)
                                    and isinstance(_other_entry_expr.qubit_positions,
                                                   ExprTuple))):
                                raise ValueError(
                                        "With exception to a symmetrically "
                                        "formed controlled-Z, the target "
                                        "of a control must be a gate or "
                                        "a multi-gate, not %s."
                                        %_other_entry_expr)
                        if not contains_cur_pos:
                            raise ValueError(
                                    "The qubit positions of a MultiQubitElem "
                                    "must contain that of the MultiQubitElem "
                                    "itself, but %s is not in %s"
                                    %(qubit_pos, qubit_positions))
            
            if has_generic_multiqubitelem:
                # If there is a generic MultiQubitElem, we need
                # a vertical wire from top to bottom since anything
                # could be the target.
                for row, _ in enumerate(col_entries[:-1]):
                    down_wire_locations.add((row, col))
            else:
                # Map minimum rows of qubit_positions to the
                # maximum of maximum rows of qubit_positions
                # (except for multigates where we skip vertical wires).
                minrow_to_maxrow = dict()
                for qubit_positions in qubit_positions_of_column:
                    if isinstance(qubit_positions, Set):
                        positions_as_tuple = qubit_positions.operands
                        assert isinstance(positions_as_tuple, ExprTuple)
                        pos_rows = [qubit_position_to_row[_qubit_pos] for
                                    _qubit_pos in positions_as_tuple.entries]
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
                        # is before the last row of MultiQubitElem
                        # qubit positions, and it isn't blocked by a
                        # multigate.
                        down_wire_locations.add((row, col))
        
        # Return all 'down wire' location.
        return down_wire_locations

    @staticmethod
    def _is_multirowcenter(center_entry):
        '''
        Return True iff the given entry is the center of an
        ExprRange over identity gates (a multiwire) or the center
        of an ExprRange over MultiQubitElems that represent a 
        multigate.
        '''
        from proveit.numbers import one
        from proveit.physics.quantum import I
        if center_entry[-1] not in ('implicit', 'explicit'):
            return False # Not the center of an ExprRange.
        range_expr = center_entry[0]
        assert isinstance(range_expr, ExprRange)
        range_expr_body = range_expr.body
        if range_expr_body == Gate(I) and range_expr.start_index==one:
            return True # A multiwire
        if not isinstance(range_expr_body, MultiQubitElem):
            # Not a multiwire or multigate.
            return False
        range_expr_param = range_expr.parameter
        if range_expr_param in free_vars(range_expr_body):
            # Cannot represent a multigate if the ExprRange body
            # depends upon the parameter.
            return False
        if isinstance(range_expr_body.qubit_positions, ExprTuple):
            # A confirmed multigate with an ExprTuple of qubit
            # positions.
            return True
        return False

    def latex(self, fence=False, **kwargs):
        from proveit.physics.quantum import (
                CONTROL, CLASSICAL_CONTROL, SWAP, SPACE)
        from proveit.numbers import one, Add, subtract
        spacing = self.get_style('spacing')
            
        # Get the element positions corresponding to each row of the
        # array, raising a ValueError if there are inconsistencies.
        vert_expr_array = self.vert_expr_array
        format_row_element_positions = (
                vert_expr_array.get_format_row_element_positions())
        
        # When we have an explicit parameterization of a
        # horizontal or vertical ExprArray, we put two dots before&after
        # or above&below.  Wrap this with the appropriate kind of
        # circuit element: \gate, \qin, \qout, etc.
        def inside_elem_wrapper(explicit_cell_latex_fn):
            def new_explicit_cell_latex_fn(expr_latex):
                assert expr_latex[-1] == '}'
                _i = expr_latex.find('{')
                return expr_latex[:_i] + (
                        '{%s}'%explicit_cell_latex_fn(expr_latex[_i:-1]))
            return new_explicit_cell_latex_fn
        
        # Get latex-formatted cells.  Indicate that these should be
        # formatted in the context of being within a Qcircuit
        format_cell_entries = []
        formatted_cells = vert_expr_array.get_latex_formatted_cells(
                format_cell_entries=format_cell_entries,
                vertical_explicit_cell_latex_fn=inside_elem_wrapper(
                        ExprArray.vertical_explicit_cell_latex),
                horizontal_explicit_cell_latex_fn=inside_elem_wrapper(
                        ExprArray.horizontal_explicit_cell_latex),
                within_qcircuit=True)
        
        width = len(formatted_cells)
        height = 1
        for formatted_col_entries in formatted_cells:
            if isinstance(formatted_col_entries, list):
                height = max(height, len(formatted_col_entries))
        
        out_str = ''
        if fence:
            out_str = r'\left('
        out_str += r'\begin{array}{c} \Qcircuit' + spacing + '{' + '\n'
        
        # Find locations where we should add a downward wire.
        down_wire_locations = Qcircuit._find_down_wire_locations(
                format_cell_entries, format_row_element_positions)
        row = 0
        formatted_entries = []
        while row < height:
            formatted_row_entries = []
            collapsible_multirow = (height > 1)
            # Continue with a wire except after a space, measurement,
            # or output:
            continue_wire = True 
            for col in range(width):
                continue_wire = True
                format_col_entries = format_cell_entries[col]
                formatted_col_entries = formatted_cells[col]
                if isinstance(formatted_col_entries, list):
                    formatted_entry = formatted_col_entries[row]
                    if (collapsible_multirow and 
                            row+1 < len(format_col_entries)):
                        next_row_entry = format_col_entries[row+1]
                        if not Qcircuit._is_multirowcenter(next_row_entry):
                            collapsible_multirow = False
                    else:
                        collapsible_multirow = False
                    entry = format_col_entries[row][0]
                    if formatted_entry in (r'\cdots', r'\vdots', r'\ddots'):
                        # Wrap ellipses in \gate, \lstick, or \rstick
                        # as appropriate.
                        _expr = entry
                        if isinstance(_expr, ExprRange):
                            _expr = _expr.body
                        # If the entry is a conditional set, use the
                        # value of any of the conditionals to determine
                        # the type.
                        while (isinstance(_expr, ConditionalSet) or
                               isinstance(_expr, Conditional)):
                            if isinstance(_expr, ConditionalSet):
                                _expr = _expr.conditionals[0]
                            if isinstance(_expr, Conditional):
                                _expr = _expr.value
                        if (isinstance(_expr, Gate) or 
                                isinstance(_expr, MultiQubitElem)):
                            formatted_entry = r'& \gate{%s}'%formatted_entry
                        elif isinstance(_expr, Input):
                            formatted_entry = r'\qin{%s}'%formatted_entry
                        elif isinstance(_expr, Output):
                            formatted_entry = r'& \qout{%s}'%formatted_entry
                            continue_wire = False
                        elif isinstance(_expr, Measure):
                            formatted_entry = r'& \measureD{%s}'%formatted_entry
                            continue_wire = False
                    if isinstance(entry, MultiQubitElem):
                        if (isinstance(entry.element, Output) or
                                isinstance(entry.element, Measure)
                                or entry.element == SPACE):
                            continue_wire = False
                        if isinstance(entry.qubit_positions, ExprTuple):
                            elem = entry.element
                            assert elem not in (
                                    CONTROL, CLASSICAL_CONTROL, SWAP)
                            # The top of a multi-gate (not a 
                            # control or swap and has explicit 
                            # qubit positions).
                            qubit_positions = entry.qubit_positions
                            assert qubit_positions.num_entries()==1
                            assert isinstance(qubit_positions[0], ExprRange)
                            _i = 0
                            _j = formatted_entry.find('{')
                            if formatted_entry[:2] == "& ":
                                _prefix = "& "
                                _i = 2
                            else:
                                _prefix = ""
                            assert formatted_entry[_i] == '\\'
                            _i += 1 # skip the '\'
                            qubit_pos = format_row_element_positions[row]
                            if (qubit_positions[0].start_index == qubit_pos):
                                # The top-most of a multi-gate.
                                formatted_entry = (
                                        # The '#' is a placeholder.
                                        # We'll go back through and
                                        # replace these later.
                                        _prefix +
                                        r"\multi" + formatted_entry[_i:_j]
                                        + '{#}' + formatted_entry[_j:])
                            else:
                                # Non-top of a multi-gate.
                                if (formatted_entry[_i:_j] == r'gate' or
                                        formatted_entry[_i:_i+13] == 
                                        r'multimeasure'):
                                    _i = _j # use regular "\ghost" 
                                formatted_entry = (
                                        _prefix + r'\ghost' 
                                        + formatted_entry[_i:])
                    elif (isinstance(entry, Output) or
                          isinstance(entry, Measure) or
                          entry == SPACE):
                        continue_wire = False
                    if (row, col) in down_wire_locations:
                        formatted_entry += r' \qwx[1]'                                
                    formatted_row_entries.append(formatted_entry)
                else:
                    # Use up and down arrows above and below to denote 
                    # an expression representing an entire column.
                    formatted_col = (r'\begin{array}{c} \uparrow \\'
                                     r'%s \\ \downarrow\end{array}'
                                     %formatted_col_entries)
                    if row==0:
                        # An expression represents the entire row: top
                        # Since the height may change as a result
                        # of collapsing multiwires/gates, just use '#'
                        # as a placeholder for now.
                        formatted_row_entries.append(
                                r'& \multigate{#}{%s}'%formatted_col)
                    else:
                        # An expression represents the entire row: not top
                        formatted_col = formatted_col_entries
                        formatted_row_entries.append(
                                '& \ghost{%s}'%formatted_col)
            multiwire_size = None
            if collapsible_multirow:
                # Collapse multiwires and multigates into a single row.
                row += 1                
                for col in range(width):
                    formatted_entry = formatted_row_entries[col]
                    if formatted_entry[:5] == r'& \qw':
                        # format a multiwire
                        _expr = format_cell_entries[col][row][0]
                        assert isinstance(_expr, ExprRange)
                        assert _expr.start_index == one
                        multiwire_size = _expr.end_index
                        formatted_row_entries[col] = (
                                r'& { /^{' + multiwire_size.latex() + r'} } '
                                + formatted_entry[2:])
                    else:
                        assert (formatted_entry[:6] == r'\ghost' or
                                formatted_entry[:8] == r'& \ghost' or
                                '{#}' in formatted_entry)
                    if continue_wire and (multiwire_size is None):
                        # We want the multi-wire size for the continued
                        # wire, so let's figure that out.
                        start = format_row_element_positions[row - 1]
                        end = format_row_element_positions[row + 1]
                        if start == one:
                            multiwire_size = end
                        else:
                            multiwire_size = Add(subtract(end, start), one)
                            multiwire_size = multiwire_size.simplified()
                row += 2
            else:
                row += 1
            if continue_wire:
                if multiwire_size is None:
                    formatted_entry = r'& \qw'
                else:
                    formatted_entry = (r'& { /^{%s} } \qw'
                                       %multiwire_size.latex())
                formatted_row_entries.append(formatted_entry)
            formatted_entries.append(formatted_row_entries)
            
        # Generate row contributions to out_str.
        height = len(formatted_entries)
        for row, formatted_row_entries in enumerate(formatted_entries):
            for col, formatted_entry in enumerate(formatted_row_entries):
                _i = formatted_entry.find('{')
                if _i >= 0 and formatted_entry[_i:_i+3]=='{#}':
                    # replace the '#' placeholder in a multigate with
                    # the appropriate number of rows.
                    _nrows = 1
                    while (row+_nrows < height and 
                           r'\ghost' in formatted_entries[row+_nrows][col][:8]):
                        _nrows += 1
                    if _nrows == 1:
                        formatted_entry = (
                                formatted_entry.replace('multi', '', 1))
                        formatted_entries[row][col] = (
                                formatted_entry.replace('{#}', '', 1))
                    else:
                        formatted_entries[row][col] = (
                                formatted_entry.replace(
                                        '{#}', '{%d}'%(_nrows-1), 1))
            out_str += ' '.join(formatted_row_entries) 
            if row == height-1:
                out_str += '\n'                
            else:
                out_str += r' \\' + '\n'
        

        out_str += r'} \end{array}'
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
