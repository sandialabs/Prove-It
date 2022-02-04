from proveit import (Expression, Function, Literal, 
                     ConditionalSet, Conditional, ExprRange,
                     ExprTuple, ExprArray, VertExprArray, ProofFailure,
                     StyleOptions, free_vars)
from proveit.logic import Equals, Set
from proveit.numbers import Interval, zero, one, num, Add, Neg
from proveit.physics.quantum.circuits.qcircuit_elements import (
        QcircuitElement, Gate, MultiQubitElem, Input, Output, Measure, 
        config_latex_tool)

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
                                  format_row_element_positions,
                                  qubit_pos_to_row):
        '''
        Return the set of (row, col) locations of the circuit
        grid where we should have a vertical wire to the next row.
        We also check for MultiQubitElem consistencies, raising
        ValueError or TypeError if there is an inconsistency.
        '''
        from proveit.physics.quantum import (
                CONTROL, CLASSICAL_CONTROL, SWAP)
        down_wire_locations = set()
        
        # Iterate over each column.
        for col, col_entries in enumerate(format_cell_entries):
            if not isinstance(col_entries, list):
                # An Expression represents the entire column.
                # There are no multi-qubit gates to worry about.
                continue
            
            # Iterate over each row. Map qubit position sets of
            # MultiQubitElems sets of rows that may be involved. 
            multiqubit_positions_of_column = set()
            # No vertical wire through multi-gate/input/output/measure
            # (blockade):
            multiqubit_blockade = set() 
            has_generic_multiqubitelem = False
            # Active multiqubit element operation/state/basis
            # of a multiqubit gate/input/output/measure:
            active_multiqubit_op = None
            # "part" of the active multiqubit operation to come next:
            next_part = None 
            for row, entry in enumerate(col_entries):
                 # The actual Expression of the entry
                entry_expr, outer_role, inner_role = entry
                if isinstance(entry_expr, ExprRange):
                    elem_param = entry_expr.parameter
                    end = entry_expr.end_index
                    entry_expr = entry_expr.body
                else:
                    elem_param = end = None
                qubit_pos = format_row_element_positions[row]
                if isinstance(entry_expr, MultiQubitElem):
                    # MultiQubitElem entry.
                    elem = entry_expr.element
                    targets = entry_expr.targets
                    if (next_part is not None and 
                            not isinstance(targets, Interval)):
                        raise ValueError(
                                "The MultiQubitElem expressions "
                                "composing a multiqubit gate/input/output"
                                "/measure must be consecutive "
                                "up until the end qubit positions: "
                                "encountered %s before end of %s"
                                %(entry_expr, active_multiqubit_op))
                    if isinstance(targets, Interval):
                        # A multi-gate/input/output/measure.  
                        # The targets must an Interval covering all of 
                        # the involved qubits and elements must 
                        # indicate consecutive "parts" starting from 1.
                        start_index = targets.lower_bound
                        end_index = targets.upper_bound
                        # This trick will remove any empty range:
                        start_index = Add(start_index, zero).quick_simplified()
                        end_index = Add(end_index, zero).quick_simplified()
                        multiqubit_positions_of_column.add(
                                (start_index, end_index))
                        if isinstance(elem, Gate):
                            elem_type = 'gate'
                            op_type = 'operation'
                        elif isinstance(elem, Input):
                            elem_type = 'input'
                            op_type = 'state'
                        elif isinstance(elem, Output):
                            elem_type = 'output'
                            op_type = 'state'
                        elif isinstance(elem, Measure):
                            elem_type = 'measure'
                            op_type = 'basis'
                        else:
                            raise ValueError(
                                    "A MultiQubitElem element should be "
                                    "a Gate/Input/Output/Measure")
                        if not hasattr(elem, 'part'):
                            raise ValueError(
                                    "A MultiQubitElem element should be "
                                    "a QcircuitElement with a 'part' "
                                    "designation")
                        elem_part = elem.part
                        # element operation/state/basis:
                        elem_op = next(elem.operands.items())[1]

                        if next_part is None:
                            diff = Add(qubit_pos, 
                                       Neg(start_index)).quick_simplified()
                            if diff != zero:
                                raise ValueError(
                                        "Mismatch of starting qubit position "
                                        "of a multigate: %s ≠ %s"
                                        %(qubit_pos, start_index))
                            if end_index not in qubit_pos_to_row:
                                raise ValueError(
                                        "%s is not known as the top qubit "
                                        "position corresponding to any row: "
                                        "%s"%(end_index, 
                                              qubit_pos_to_row))
                            next_part = one
                            active_multiqubit_op = elem_op
                        else:
                            if elem_op != active_multiqubit_op:
                                raise ValueError(
                                        "The MultiQubitElem expressions "
                                        "composing a multi%s must use "
                                        "the same %s: %s ≠ %s"%
                                        (elem_type, op_type, 
                                         elem_op, active_multiqubit_op))
                        if inner_role in ('implicit', 'explicit', 
                                          'param_independent'):
                            if elem_part != elem_param:
                                raise ValueError(
                                        "An ExprRange of multi%ss should be "
                                        "parameterized by the parts: "
                                        "%s ≠ %s"%(elem_type, elem_part, 
                                                   elem_param))
                        elif outer_role not in ('implicit', 'explicit', 
                                                'param_independent'):
                            if elem_part != next_part:
                                raise ValueError(
                                        "Part indices must be consecutive "
                                        "starting from 1: %s ≠ %s"%(
                                                elem_part, next_part))
                        if qubit_pos == end_index:
                            active_multiqubit_op = None
                            next_part = None
                        elif elem_param is None:
                            next_part = Add(elem_part, one).quick_simplified()
                        else:
                            next_part = end # next up, end of range.
                        if active_multiqubit_op is not None:
                            # There is a continuing multigate, so block
                            # any down wire from this row.
                            multiqubit_blockade.add(row)
                    elif isinstance(targets, Set):
                        # Explicit targets for a control, swap,
                        # or multi-qubit gate/input/output/measure
                        # operation.
                        if elem not in (CONTROL, CLASSICAL_CONTROL, SWAP):
                            if not isinstance(targets, Interval):
                                raise ValueError(
                                        "To format a multi-gate/input/output/"
                                        "measure in a Qcircuit, the targets must " 
                                        "be an Interval, not %s"
                                        %targets)
                        multiqubit_positions_of_column.add(
                                (qubit_pos,) + targets.operands.entries)
                        
                        # For a control or a swap, make sure the 
                        # targets all exist and have appropriate
                        # entries.

                        # If it is a SWAP, it should have 1 target
                        # (and that target should target this qubit
                        # mutually).
                        if (elem == SWAP and not targets.operands.is_single()):
                            raise ValueError(
                                    "For a SWAP, please use 1 target, "
                                    "not %d"%targets.num_entries())
                        
                        # Other cases (e.g., a control with many
                        # targets), should have 
                        for _other_pos in targets.operands:
                            if _other_pos == qubit_pos:
                                raise ValueError(
                                        "A %s should not have itself as "
                                        "a target."%elem)
                            if _other_pos not in qubit_pos_to_row:
                                raise ValueError(
                                        "The target of %s for a %s "
                                        "is not an explicit qubit position "
                                        "of the Qcircuit, it is not in %s"
                                        %(_other_pos, elem,
                                          qubit_pos_to_row.keys()))
                            _other_row = qubit_pos_to_row[_other_pos]
                            _other_entry_expr = col_entries[_other_row][0]
                            if elem == SWAP:
                                if _other_entry_expr != entry_expr:
                                    raise ValueError(
                                            "For a SWAP, please use "
                                            "two MultiQubitElems that are "
                                            "the same: %s ≠ %s."
                                            %(_other_entry_expr, entry_expr))
                            if isinstance(_other_entry_expr, MultiQubitElem):
                                other_targets = (
                                        _other_entry_expr.targets)
                                if isinstance(other_targets, Interval):
                                    other_top_pos = Add(
                                            other_targets.lower_bound, 
                                            zero).quick_simplified()
                                    if (other_top_pos != _other_pos):
                                        raise ValueError(
                                                "A %s MultiQubitElem should "
                                                "not target part of a "
                                                "mult-gate except the top.")
                                    if (_other_entry_expr.element.part != one):
                                        raise ValueError(
                                                "A %s MultiQubitElem should "
                                                "not target part of a "
                                                "mult-gate except part 1.")
                                elif _other_entry_expr == CONTROL:
                                    # A CONTROL may only target another
                                    # CONTRROL if it is mutual.
                                    valid = False
                                    if (targets.is_single() and
                                            other_targets.is_single() and
                                            other_targets[0] in 
                                            qubit_pos_to_row):
                                        other_target = other_targets[0]
                                        other_target_row = (
                                            qubit_pos_to_row[other_target])
                                        if other_target_row == row:
                                            valid = True
                                    if not valid:
                                        raise ValueError(
                                                "A CONTROL may only target "
                                                "another CONTROL if it is "
                                                "mutual: %s and %s aren't "
                                                "mutual on %s and %s."
                                                %(targets, other_targets,
                                                  row, _other_row))                                
                            elif not isinstance(_other_entry_expr, Gate):
                                raise ValueError(
                                        "With exception to a symmetrically "
                                        "formed controlled-Z, the target "
                                        "of a control must be a gate or "
                                        "a multi-gate, not %s."
                                        %_other_entry_expr)
                    else:
                        # A "generic" MultiQubitElem (no explicit
                        # targets).
                        has_generic_multiqubitelem = True
            
            if has_generic_multiqubitelem:
                # If there is a generic MultiQubitElem, we need
                # a vertical wire from top to bottom since anything
                # could be the target.
                for row, _ in enumerate(col_entries[:-1]):
                    down_wire_locations.add((row, col))
            else:
                # Map minimum rows of multiqubit_positions to the
                # maximum of maximum rows of multiqubit_positions
                # (except for multigates where we skip vertical wires).
                minrow_to_maxrow = dict()
                for multiqubit_positions in multiqubit_positions_of_column:
                    pos_rows = [qubit_pos_to_row[_qubit_pos] for
                                _qubit_pos in multiqubit_positions]
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
                            and row not in multiqubit_blockade):
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
        if center_entry[-1] not in ('implicit', 'explicit', 
                       'param_independent'):
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
        if isinstance(range_expr_body.targets, Interval):
            # A confirmed multigate with an Interval of "targets".
            return True
        return False

    def latex(self, fence=False, **kwargs):
        from proveit.physics.quantum import (
                CONTROL, CLASSICAL_CONTROL, SWAP, SPACE)
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
            def new_explicit_cell_latex_fn(expr_latex, nested_range_depth):
                _i = expr_latex.find('{')
                if (_i > 0 and (
                        expr_latex[:_i] in (r'\gate', r'\qin', r'\qout')
                        or expr_latex[:8]==r'\measure')):
                    print("THERE", expr_latex)
                    assert expr_latex[-1] == '}'
                    return expr_latex[:_i] + (
                            '{%s}'%explicit_cell_latex_fn(
                                    expr_latex[_i:-1], nested_range_depth))
                return explicit_cell_latex_fn(
                        expr_latex, nested_range_depth)
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
        qubit_position_to_row = {pos:row for row, pos in 
                                 enumerate(format_row_element_positions)}
        down_wire_locations = Qcircuit._find_down_wire_locations(
                format_cell_entries, format_row_element_positions,
                qubit_position_to_row)
        
        # Map VertExprArray rows to number of rows the may be collapsed
        # into one in the Qcircuit where applicable (with matching
        # multi-wire/gate/input/output/measure).
        row_to_collapse_count = dict()
        for row in range(height):
            is_multirow_center = True
            multirow_front_expansions = set()
            multirow_back_expansions = set()
            for col in range(width):
                format_col_entries = format_cell_entries[col]
                if not isinstance(format_col_entries, list):
                    # The entire column is represented by a single
                    # expression, so let's skip this.
                    continue
                entry = format_col_entries[row]
                if not Qcircuit._is_multirowcenter(entry):
                    is_multirow_center = False
                else:
                    range_expr = entry[0]
                    front_expansion = int(range_expr.get_style(
                            'front_expansion'))
                    back_expansion = int(range_expr.get_style(
                            'back_expansion'))
                    multirow_front_expansions.add(front_expansion)
                    multirow_back_expansions.add(back_expansion)
            if len(multirow_front_expansions) == 0:
                # Must only have entire columns represented.
                is_multirow_center = False
            if is_multirow_center:
                # For the VertExprArray to be lined up properly,
                # the ExprRange expansions must be the same along a
                # row.
                assert (len(multirow_front_expansions) == 1 and
                        len(multirow_back_expansions) == 1), (
                                "Should have been caught in ExprArray "
                                "alignment check.")
                front_expansion = next(iter(multirow_front_expansions))
                back_expansion = next(iter(multirow_back_expansions))
                row_to_collapse_count[row-front_expansion] = (
                        front_expansion, back_expansion)
        # Generate the formatted entries.
        row = 0
        formatted_entries = []
        while row < height:
            formatted_row_entries = []
            # Continue with a wire except after a space, measurement,
            # or output:
            continue_wire = True 
            for col in range(width):
                continue_wire = True
                format_col_entries = format_cell_entries[col]
                formatted_col_entries = formatted_cells[col]
                if isinstance(formatted_col_entries, list):
                    formatted_entry = formatted_col_entries[row]
                    entry, outer_role, inner_role = format_col_entries[row]
                    if isinstance(entry, ExprRange):
                        entry = entry.body
                    multi_op = False
                    if isinstance(entry, MultiQubitElem):
                        if (isinstance(entry.element, Output) or
                                isinstance(entry.element, Measure)
                                or entry.element == SPACE):
                            continue_wire = False
                        if isinstance(entry.targets, Interval):
                            multi_op = True
                            elem = entry.element
                            # Double-checking (should have been checked
                            # in _find_down_wire_locations):
                            assert elem not in (
                                    CONTROL, CLASSICAL_CONTROL, SWAP)
                            # A multi-gate/input/output (not a 
                            # control or swap and has explicit 
                            # qubit positions).
                            targets = entry.targets
                            top_qubit_pos = Add(
                                    targets.lower_bound,
                                    zero).quick_simplified()
                            top_row = qubit_position_to_row[top_qubit_pos]
                            formatted_entry = formatted_col_entries[top_row]
                            if outer_role in ('implicit', 'explicit',
                                              'param_independent'):
                                # Implicit/explicit ellipsis along the
                                # top row of a multi-circuit-entry.
                                formatted_entry = (r'& \gate{%s}'
                                                   %formatted_entry)
                                # We can forget about roles -- we've
                                # taken care of it.
                                inner_role = outer_role = None
                            _i = 0
                            _j = formatted_entry.find('{')
                            if formatted_entry[:2] == "& ":
                                _prefix = "& "
                                _i = 2
                            else:
                                _prefix = ""
                            assert formatted_entry[_i] == '\\'
                            _i += 1 # skip the '\'
                            if row==top_row:
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
                                        formatted_entry[_i:_i+7] == 
                                        r'measure'):
                                    _i = _j # use regular "\ghost" 
                                formatted_entry = (
                                        _prefix + r'\ghost' 
                                        + formatted_entry[_i:])
                    elif (isinstance(entry, Output) or
                          isinstance(entry, Measure) or
                          entry == SPACE):
                        continue_wire = False
                    if (not multi_op and 
                            not {inner_role, outer_role}.isdisjoint(
                                    ('implicit', 'explicit',
                                     'param_independent'))):
                        # Wrap ellipses in \gate, \qin, \qout, 
                        # or \measure... as appropriate.
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
                            formatted_entry = (r'& \measure{%s} \qw'
                                               %formatted_entry)
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
                        formatted_row_entries.append(
                                '& \ghost{%s}'%formatted_col)
            multiwire_size = None
            if row in row_to_collapse_count:
                # Collapse multiwires and multigates into a single row.
                front_expansion, back_expansion = row_to_collapse_count[row]
                row += front_expansion
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
                        multiwire_size = Add(
                                end, Neg(start),
                                num(front_expansion+back_expansion-1))
                        multiwire_size = multiwire_size.quick_simplified()
                row += back_expansion + 1
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

class QcircuitSet(Literal):
    '''
    Represents the set of all consistent quantum circuits.
    '''
    def __init__(self, *, styles=None):
        Literal.__init__(
            self, string_format='QC', latex_format=r'\mathbb{Q.C.}',
            styles=styles)
    
