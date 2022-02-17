from proveit import (Expression, Function, Literal, IndexedVar,
                     ConditionalSet, Conditional, ExprRange,
                     ExprTuple, ExprArray, VertExprArray, ProofFailure,
                     StyleOptions, free_vars, prover, relation_prover,
                     defaults, safe_dummy_var, TransRelUpdater)
from proveit import i, j, k, l, m, n, A, U, V, N
from proveit.core_expr_types import n_k
from proveit.logic import Equals, Set, InSet
from proveit.numbers import (Interval, zero, one, two, num, Add, Neg, Mult,
                             subtract, is_literal_int, quick_simplified_index)
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
                                  qubit_pos_to_row,
                                  implicit_format_col_row_pairs):
        '''
        Return the set of (row, col) locations of the circuit
        grid where we should have a vertical wire to the next row.
        We also check for MultiQubitElem consistencies, raising
        ValueError or TypeError if there is an inconsistency.
        
        Populate col_row_to_latex_kwargs appropriately while we
        are at it: (col, row) -> kwargs for formatting.
        '''
        from proveit.physics.quantum import (
                CONTROL, CLASSICAL_CONTROL, SWAP, I)
        down_wire_locations = set()
                
        # Iterate over each column.
        for col, col_entries in enumerate(format_cell_entries):
            if not isinstance(col_entries, list):
                # An Expression represents the entire column.
                # There are no multi-qubit gates to worry about.
                # (It shouldn't make a difference, but use 
                # 'explicit_kwargs' just in case.)
                continue
            
            # Iterate over each row. Map qubit position sets of
            # MultiQubitElems sets of rows that may be involved. 
            multiqubit_positions_of_column = set()
            # No vertical wire through multi-gate/input/output/measure
            # (blockade):
            multiqubit_blockade = set() 
            has_generic_multigateelem = False
            top_nontrivial_row = None
            bottom_nontrivial_row = None
            # Active multiqubit element operation/state/basis
            # of a multiqubit gate/input/output/measure:
            active_multiqubit_op = None
            # "part" of the active multiqubit operation to come next:
            next_part = None 
            for row, entry in enumerate(col_entries):
                 # The actual Expression of the entry
                entry_expr, outer_role, inner_role = entry
                if isinstance(entry_expr, ExprRange):
                    assert not {inner_role, outer_role}.isdisjoint(
                            {'implicit', 'explicit', 'param_independent'})
                    elem_param = entry_expr.parameter
                    entry_expr = entry_expr.body
                else:
                    elem_param = None
                if not (isinstance(entry_expr, Gate) and 
                        entry_expr.operation == I):
                    if top_nontrivial_row is None:
                        top_nontrivial_row = row
                    bottom_nontrivial_row = row
                qubit_pos = format_row_element_positions[row]
                # Explicit formatting is the default but may be changed
                # to implicit formatting below if there is a reason.
                if qubit_pos is None and active_multiqubit_op is None:
                    # This is an 'ellipsis' portion but there is no
                    # active_multiqubit_op, so just use explicit
                    # keyword args for formatting and move on.
                    if (isinstance(entry_expr, Gate) and 
                            entry_expr.operation == I):
                        # Just an identity -- do this to allow a
                        # multiwire collapse if possible.
                        implicit_format_col_row_pairs.add((col, row))
                    continue
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
                        start_index = quick_simplified_index(start_index)
                        end_index = quick_simplified_index(end_index)
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

                        if active_multiqubit_op is None:
                            diff = Add(qubit_pos, 
                                       Neg(start_index)).quick_simplified()
                            if diff != zero:
                                # There is no obvious match for the 
                                # starting qubit position of the 
                                # multigate; so, let's use explicit 
                                # formatting.
                                has_generic_multigateelem = True
                                continue
                            if end_index not in qubit_pos_to_row:
                                # The end index is not known as the
                                # qubit position on any row; so, let's 
                                # use explicit formatting.
                                has_generic_multigateelem = True
                                continue
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
                            if (next_part is not None 
                                    and elem_part != next_part):
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
                            # We don't yet know the next part after an
                            # ellipses -- that's okay.
                            next_part = None
                        if active_multiqubit_op is not None:
                            # There is a continuing multigate, so block
                            # any down wire from this row.
                            multiqubit_blockade.add(row)
                        multiqubit_positions_of_column.add(
                                (start_index, end_index))
                        implicit_format_col_row_pairs.add((col, row))
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
                        implicit_format_col_row_pairs.add((col, row))
                    else:
                        if (not isinstance(entry_expr.element, QcircuitElement)
                                or isinstance(entry_expr.element, Gate)):
                            # A "generic" unknown or multi-gate element 
                            # (no explicit targets).
                            has_generic_multigateelem = True
                elif not isinstance(entry_expr, QcircuitElement):
                    # The entry is not a QcircuitElement -- it could
                    # represent any kind of element.
                    has_generic_multigateelem = True
            
            if has_generic_multigateelem:
                # If there is a generic MultiQubitElem, we need
                # a vertical wire from topmost nontrivial row to 
                # the bottommost nontrivial row since anything
                # could be the target.
                if top_nontrivial_row is not None:
                    for row in range(top_nontrivial_row,
                                     bottom_nontrivial_row):
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
                    assert expr_latex[-1] == '}'
                    return expr_latex[:_i] + (
                            '{%s}'%explicit_cell_latex_fn(
                                    expr_latex[_i:-1], nested_range_depth))
                return explicit_cell_latex_fn(
                        expr_latex, nested_range_depth)
            return new_explicit_cell_latex_fn

        # Find locations where we should add a downward wire.
        # At the same time, we will determine which cells should use
        # an "implicit" representation (where we don't explicitly
        # show part numbers or targets because it is clear from the
        # diagram.) 
        qubit_position_to_row = {pos:row for row, pos in 
                                 enumerate(format_row_element_positions)}
        format_cell_entries = vert_expr_array.get_format_cell_entries()
        implicit_format_col_row_pairs = set()
        down_wire_locations = Qcircuit._find_down_wire_locations(
                format_cell_entries, format_row_element_positions,
                qubit_position_to_row, implicit_format_col_row_pairs)
        explicit_kwargs = {'within_qcircuit':True, 'show_explicitly':True}
        implicit_kwargs = {'within_qcircuit':True, 'show_explicitly':False}
        width = len(format_cell_entries)
        height = 1
        col_row_to_latex_kwargs = dict()
        for col in range(width):
            format_col_entries = format_cell_entries[col]
            if isinstance(format_col_entries, list):
                height = max(height, len(format_col_entries))
                for row in range(height):
                    if (col, row) in implicit_format_col_row_pairs:
                        col_row_to_latex_kwargs[(col, row)] = implicit_kwargs
                    else:
                        col_row_to_latex_kwargs[(col, row)] = explicit_kwargs
            else:
                col_row_to_latex_kwargs[(col,)] = explicit_kwargs
        
        # Get latex-formatted cells.  Indicate that these should be
        # formatted in the context of being within a Qcircuit
        formatted_cells = vert_expr_array.get_latex_formatted_cells(
                format_cell_entries=format_cell_entries,
                vertical_explicit_cell_latex_fn=inside_elem_wrapper(
                        ExprArray.vertical_explicit_cell_latex),
                horizontal_explicit_cell_latex_fn=inside_elem_wrapper(
                        ExprArray.horizontal_explicit_cell_latex),
                col_row_to_latex_kwargs=col_row_to_latex_kwargs)
                
        out_str = ''
        if fence:
            out_str = r'\left('
        out_str += r'\begin{array}{c} \Qcircuit' + spacing + '{' + '\n'        
        
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
                if ((col, row) not in implicit_format_col_row_pairs or 
                        not Qcircuit._is_multirowcenter(entry)):
                    is_multirow_center = False
                else:
                    range_expr = entry[0]
                    front_expansion = range_expr.get_front_expansion()
                    back_expansion = range_expr.get_back_expansion()
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
            if row in row_to_collapse_count:
                # Collapse multiwires and multigates into a single row.
                front_expansion, back_expansion = row_to_collapse_count[row]
                next_row = row + front_expansion + 1 + back_expansion
            else:
                next_row = row + 1
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
                        if (isinstance(entry.targets, Interval) and 
                                (col, row) in implicit_format_col_row_pairs):
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
                            _expr = _expr.innermost_body()
                        # If the entry is a conditional set, use the
                        # value of any of the conditionals to determine
                        # the type.
                        while (isinstance(_expr, ConditionalSet) or
                               isinstance(_expr, Conditional)):
                            if isinstance(_expr, ConditionalSet):
                                _expr = _expr.conditionals[0]
                            if isinstance(_expr, Conditional):
                                _expr = _expr.value
                        if isinstance(_expr, MultiQubitElem):
                            _expr = _expr.element
                        if (isinstance(_expr, Gate) or 
                                not isinstance(_expr, QcircuitElement)):
                            # A gate/multigate or unknown element.
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
                    elif not isinstance(entry, QcircuitElement):
                        # This entry is not a Qcircuit element,
                        # so it could represent anything.  Wrap it
                        # in \gate.
                        formatted_entry = r'& \gate{%s}'%formatted_entry
                    if (next_row-1, col) in down_wire_locations:
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
                    '''
                    else:
                        # It can also by r'& \gate{\cdots}'.
                        # Let's just forget about this check for now.
                        assert (formatted_entry[:6] == r'\ghost' or
                                formatted_entry[:8] == r'& \ghost' or
                                '{#}' in formatted_entry)
                    '''
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
    
    @prover
    def concatenate(self, extension, **defaults_config):
        '''
        If this is a valid quantum circuit (in Q.C.), and
        the given extension is also valid quantum circuit,
        and the outputs of this circuit and the inputs of the
        following circuit match, we can join them together
        into a longer valid circuit (in Q. C.).
        '''
        from . import concatenation
        _U = self.vert_expr_array[:-1]
        _V = extension.vert_expr_array[1:]
        _i = _U.num_elements()
        _j = _V.num_elements()
        self_out = self.vert_expr_array[-1]
        ext_in = extension.vert_expr_array[0]
        out_repl_map = self._repl_map_for_input_or_output(Output, 
                                                          self_out)
        in_repl_map = self._repl_map_for_input_or_output(Input, 
                                                         ext_in)
        if out_repl_map != in_repl_map:
            raise ValueError("This output must match the extension's "
                             "input in order to concatenate")
        repl_map = out_repl_map.update({i:_i, j:_j, U:_U, V:_V})
        impl = concatenation.instantiate(repl_map)
        return impl.derive_consequent()

    @prover
    def trivially_expand(self, wires_above, wires_below, **defaults_config):
        '''
        If this is a valid quantum circuit (in Q.C.), prove an expanded
        form with plain wires added above and/or below is also valid.
        '''
        from . import trivial_expansion
        _A = self.vert_expr_array
        _m = wires_above
        _n = wires_below
        _k = _A.num_elements()
        _l = _A[0].num_elements()
        impl = trivial_expansion.instantiate(
                {k:_k, l:_l, m:_m, n:_n, A:_A})
        return impl.derive_consequent()

    @relation_prover
    def input_consolidation(self, **defaults_config):
        '''
        Return a quantum circuit equivalence between this quantum
        circuit and one in which all of the inputs have been
        consolidated into one encompassing input state (as the
        tensor product of the original input states).
        '''
        from . import input_consolidation
        return self._in_or_out_consolidation(
                Input, self.vert_expr_array[0], input_consolidation)

    @relation_prover
    def output_consolidation(self, **defaults_config):
        '''
        Return a quantum circuit equivalence between this quantum
        circuit and one in which all of the outputs have been
        consolidated into one encompassing output state (as the
        tensor product of the original output states).
        '''
        from . import output_consolidation
        return self._in_or_out_consolidation(
                Output, self.vert_expr_array[-1], output_consolidation)

    def _in_or_out_consolidation(self, elem_type, col, thm):
        repl_map = self._repl_map_for_input_or_output(elem_type, col)
        defaults.test_repl_map = repl_map
        consolidation = thm.instantiate(repl_map)
        # Now consolidate ExprRanges that may have been split
        # in the process of lining up N_{k-1} entries with N_k entries.
        
        '''
        _A, _m, _n, _N = Qcircuit._extract_input_or_output(elem_type, col)
        _k = safe_dummy_var(_m)
        N_0_to_m = ExprRange(_k, IndexedVar(N, _k), zero, _m)
        
        # There is a bit of gymnastics here to match ExprRange
        # indices which we shoulb be able to simplify in the future.
        
        N_alt1 = N_0_to_m.partition(zero).rhs
        N_alt2 = N_0_to_m.partition(subtract(_m, one)).rhs

        # Need these proofs::
        _0_to_m = ExprRange(_k, _k, zero, _m)
        _0_to_m.partition(zero)
        _0_to_m.partition(subtract(_m, one))
        
        defaults.test_repl_map = {A:_A, m:_m, n:_n, N:_N, N_alt1:_N, N_alt2:_N}
        consolidation = thm.instantiate(
                {A:_A, m:_m, n:_n, N:_N, N_alt1:_N, N_alt2:_N})
        '''
        
        defaults.test_out = consolidation
        
        if not self.vert_expr_array.is_single():
            return consolidation.substitution(self)
        return consolidation.without_wrapping()
    
    @staticmethod
    def _repl_map_for_input_or_output(elem_type, col):
        from proveit.numbers import zero, one, Add
        repl_map = dict()
        
        # Get the input/output states and the number of qubits for
        # each.
        _A = []
        _n = []
        for entry in col.entries:
            if isinstance(entry, ExprRange):
                body = entry.innermost_body()
                if isinstance(body, elem_type):
                    _A.append(ExprRange(entry.parameter, body.state,
                                        entry.start_index, entry.end_index,
                                        styles=entry.get_styles()))
                    _n.append(ExprRange(entry.parameter, one, 
                                        entry.start_index, entry.end_index,
                                        styles=entry.get_styles()))
                    continue # Good
                if (isinstance(body, MultiQubitElem)
                        and isinstance(body.element, elem_type)):
                    _A.append(body.element.state)
                    _n.append(entry.num_elements(proven=False))
                    continue # Good
            elif isinstance(entry, elem_type):
                _A.append(entry.state)
                _n.append(one)
                continue # Good
            if elem_type == Input:
                raise ValueError(
                        "To perform an 'input_consolidation', the first "
                        "column of the Qcircuit must contain all valid "
                        "Input elements: %s is not suitable."%entry)
            else:
                assert elem_type == Output
                raise ValueError(
                        "To perform an 'output_consolidation', the last "
                        "column of the Qcircuit must contain all valid "
                        "Output elements: %s is not suitable."%entry)
        _A = ExprTuple(*_A)
        repl_map[m] = _m = _A.num_elements()
        _n = ExprTuple(*_n)
                
        # Get the partial sums for the numbers of qubits.
        _N = [zero]
        _Nk = zero
        for _k, _nk in enumerate(_n.entries):
            if isinstance(_nk, ExprRange):
                if _nk.is_parameter_independent:
                    # n_i, ..., n_j = x, ..., x
                    # N_k = N_{i-1} + (k-i+1)*x
                    param = safe_dummy_var(_nk, _Nk)
                    body = Add(_Nk, Mult(Add(param, Neg(_nk.start_index), 
                                             one),
                                         _nk.body))
                    start, end = _nk.start_index, _nk.end_index
                    assumptions = defaults.assumptions + (
                            InSet(param, Interval(start, end)),)                    
                    body = body.simplified(assumptions=assumptions)
                    Nks = ExprRange(param, body, start, end)
                    _Nk = Add(_Nk, subtract(end, start), one).simplified()
                else:
                    raise NotImplementedError(
                            "An ExprRange of parameter independent qubit "
                            "counts is not currently supported")
                _N.append(Nks)
            else:
                _Nk = Add(_Nk, _nk).simplified()
                _N.append(_Nk)
        repl_map[N] = _N = ExprTuple(*_N)
        
        # Now we need to partition ranges so we can align the entries of
        # N_{0}, ..., N_{m-1} with
        # N_{1}, ..., N_{m} and n_{1}, ..., n_{m}
        
        _k = safe_dummy_var(_m)
        # N_0, ..., N_m
        N_0_to_m = ExprRange(_k, IndexedVar(N, _k), zero, _m)
        # N_0, N_1, ..., N_m
        N_0_1_to_m = N_0_to_m.partition(zero).rhs
        # N_0, ..., N_{m-1}, N_m
        N_0_to_mm1_m = N_0_to_m.partition(subtract(_m, one)).rhs

        # Need these proofs as well (would be good to automate)
        _0_to_m = ExprRange(_k, _k, zero, _m)
        _0_to_m.partition(zero)
        _0_to_m.partition(subtract(_m, one))
        
        expr_for_nk = _n
        expr_for_Ak = _A
        expr_for_Nk = expr_for_Nkm1 = _N
        eq_for_Ak = TransRelUpdater(_A)
        eq_for_nk = TransRelUpdater(_n)
        eq_for_Nk = TransRelUpdater(_N)
        eq_for_Nkm1 = TransRelUpdater(_N)
        _idx = 0
        for entry in _N:
            if isinstance(entry, ExprRange):
                # We must split off the first of the entry
                # for the N_1, ..., N_m segment and the last entry for
                # the N_0, ..., N_{m-1} segment so the entries line up.
                expr_for_Nk = eq_for_Nk.update(
                        expr_for_Nk.inner_expr()[_idx].partition(
                                entry.start_index,
                                force_to_treat_as_increasing=True))
                # We have to do the same for n_1, ..., n_k and 
                # A_1, ..., A_k to match N_1, ..., N_k:
                # (uses _idx-1 since there is no n_0).
                expr_for_nk = eq_for_nk.update(
                        expr_for_nk.inner_expr()[_idx-1].partition(
                                entry.start_index,
                                force_to_treat_as_increasing=True))                
                expr_for_Ak = eq_for_Ak.update(
                        expr_for_Ak.inner_expr()[_idx-1].partition(
                                entry.start_index,
                                force_to_treat_as_increasing=True))                
                # Shift the start index in N_0, ..., N_{m-1} to line
                # it up with N_1, ..., N_{m}:
                expr_for_Nkm1 = eq_for_Nkm1.update(
                        expr_for_Nkm1.inner_expr()[_idx].shift_equivalence(
                                new_start=expr_for_Nk[_idx+1].start_index,
                                force_to_treat_as_increasing=True))
                expr_for_Nkm1 = eq_for_Nkm1.update(
                        expr_for_Nkm1.inner_expr()[_idx].partition(
                                subtract(expr_for_Nkm1[_idx].end_index, one),
                                force_to_treat_as_increasing=True))
                _idx += 2 # Add an extra 1 to account for new partition.
            else:
                _idx += 1
        repl_map[A] = expr_for_Ak
        repl_map[n] = expr_for_nk
        repl_map[N_0_1_to_m] = expr_for_Nk
        repl_map[N_0_to_mm1_m] = expr_for_Nkm1
        return repl_map
        
    
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
