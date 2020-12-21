import sys
from proveit import Literal, Operation, Lambda
from proveit.multi_expression import ExpressionTensor, Block
from proveit.logic import Forall, InSet, Equals
#from proveit.computer_science.regular_expressions import KleeneRepetition

pkg = __package__

# quantum circuit gate literals

"""
# A BARRIER is required to separate independent gates that operate in parallel
# and are adjacent in a quantum circuit (e.g., no controlled gate between them):
BARRIER = literals.add('BARRIER', {STRING:'|', LATEX:'|'})
"""

"""
class ImplicitIdentities(Block):
    '''
    ImplicitIdentities are used in quantum circuits where they must be
    filled in with one or more identities as determined by the width of
    the circuit (which isn't established until Blocks are instantiated).
    See ForallWithImplicitIdentities.
    '''
    def __init__(self, name, format_map = None):
        Block.__init__(self, name, format_map)
"""

"""    
def are_identities(gates):
    '''
    Returns the expression that the set of gates, as a List, are in the set of repeating identities.
    In other words, an expression that is true if all of the gates are identity gates.
    '''
    return In(List(gates), KleeneRepetition(I))



def _defineAxioms():
    return None # For now, we're just asserting the theorems without proof.

def _defineTheorems():
    _firstTheorem = \
    identity_collapse = ForallWithImplicitIdentities([Aetc, multi_b, Is], Equals(Circuit(Aetc, Gates(Is), multi_b), Circuit(Aetc, multi_b)))
    reverse_cz_dn = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is], Equals(Circuit(Aetc, Gates(multi_b, Target(Z), Is, CTRL_UP, Cetc), multi_d), 
                                                                                            Circuit(Aetc, Gates(multi_b, CTRL_DN, Is, Target(Z), Cetc), multi_d)))
    reverse_cz_up = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is], Equals(Circuit(Aetc, Gates(multi_b, CTRL_DN, Is, Target(Z), Cetc), multi_d), 
                                                                                            Circuit(Aetc, Gates(multi_b, Target(Z), Is, CTRL_UP, Cetc), multi_d)))
    reverse_cnot_dn_to_up = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is, IsB, IsC], 
                                                     Equals(Circuit(Aetc, Gates(multi_b, CTRL_DN, Is, Target(X), Cetc), multi_d), 
                                                            Circuit(Aetc, Gates(IsB, H, Is, H, IsC), Gates(multi_b, Target(X), Is, CTRL_UP, Cetc), Gates(IsB, H, Is, H, IsC), multi_d)))
    reverse_cnot_up_to_dn = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is, IsB, IsC], 
                                                     Equals(Circuit(Aetc, Gates(multi_b, Target(X), Is, CTRL_UP, Cetc), multi_d), 
                                                            Circuit(Aetc, Gates(IsB, H, Is, H, IsC), Gates(multi_b, CTRL_DN, Is, Target(X), Cetc), Gates(IsB, H, Is, H, IsC), multi_d)))
    return _firstTheorem, locals()
"""
            
class Input(Operation):
    '''
    Represents an input state entering from the left of the circuit
    '''
    
    def __init__(self, state):
        '''
        Create a INPUT operation with the given input state.
        '''    
        Operation.__init__(self, INPUT, state)
        self.state = state

    def formatted(self, format_type, fence=False):
        formatted_state = self.state.formatted(format_type, fence=False)
        if format_type == LATEX:
            return r'\lstick{' + formatted_state + r'}' 
        else: return Operation.formatted(self, format_type, fence)

INPUT = Literal(pkg, 'INPUT', operation_maker = lambda operands : Input(*operands)) # An input state (entering the left of the circuit)

class Output(Operation):
    '''
    Represents an input state entering from the left of the circuit
    '''
    
    def __init__(self, state):
        '''
        Create a INPUT operation with the given input state.
        '''    
        Operation.__init__(self, OUTPUT, state)
        self.state = state
    
    def formatted(self, format_type, fence=False):
        formatted_state = self.state.formatted(format_type, fence=False)
        if format_type == LATEX:
            return r'\rstick{' + formatted_state + r'} \qw' 
        else: return Operation._formatted(self, format_type, fence)

OUTPUT = Literal(pkg, 'OUTPUT', operation_maker = lambda operands : Output(*operands)) # An output state (exiting the right of the circuit)

class Gate(Operation):
    '''
    Represents a gate in a quantum circuit.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('GATE', theory=__file__)
    
    def __init__(self, gate_operation):
        '''
        Create a quantum circuit gate performing the given operation.
        '''    
        Operation.__init__(self, Gate._operator_, gate_operation)
        self.gate_operation = self.operands[0]
    
    def _formatted(self, format_type, fence=False):
        formatted_gate_operation = (
                self.gate_operation.formatted(format_type, fence=False))
        if format_type == 'latex':
            return r'\gate{' + formatted_gate_operation + r'}' 
        else: return Operation.formatted(self, format_type, fence)

# GATE = Literal(pkg, 'GATE', operation_maker = lambda operands : Gate(*operands))

class Target(Operation):
    '''
    Represents the target of a control.
    '''
    
    def __init__(self, target_gate):
        '''
        Create a Target operation with the given target_gate as the type
        of the gate for the target (e.g., X for CNOT and Z for Controlled-Z).
        '''    
        Operation.__init__(self, TARGET, target_gate)
        self.target_gate = target_gate

    def formatted(self, format_type, fence=False):
        formatted_gate_operation = self.target_gate.formatted(format_type, fence=False)
        if format_type == LATEX:
            return r'\gate{' + formatted_gate_operation + r'}' 
        else: return Operation.formatted(self, format_type, fence)

TARGET = Literal(pkg, 'TARGET', {STRING:'TARGET', LATEX:r'\targ'}, lambda operands : Target(*operands))

class MultiWire(Operation):
    '''
    Marks a "wire" as a bundle with a number of individual wires.
    '''
    
    def __init__(self, number):
        '''
        Create a multi-wire.
        '''    
        Operation.__init__(self, MULTI_WIRE, number)
        self.number = number
    
    def formatted(self, format_type, fence=False):
        formatted_number = self.number.formatted(format_type, fence=False)
        if format_type == LATEX:
            return r'/^{' + formatted_number + r'} \qw' 
        else: return Operation.formatted(self, format_type, fence)

MULTI_WIRE = Literal(pkg, 'MULTI_WIRE', operation_maker = lambda operands : MultiWire(*operands))

class Circuit(Operation):
    '''
    Represents a quantum circuit as a 2-D ExpressionTensor.
    '''
    def __init__(self, tensor, shape=None):
        '''
        Create a Circuit either with a dense tensor (list of lists ... of lists) or
        with a dictionary mapping pairs of indices to Expression elements or blocks,
        composing an ExpressionTensor.
        '''
        from .common import PASS
        if not isinstance(tensor, dict):
            # remove identity gates -- these are implicit
            tensor, _ = ExpressionTensor.TensorDictFromIterables(tensor)
        fixed_shape = (shape is not None)
        if not fixed_shape:
            shape = (0, 0)
        for idx in list(tensor.keys()):
            if len(idx) != 2:
                raise ValueError('Circuit operand must be a 2-D ExpressionTensor')
            if not fixed_shape:
                shape = (max(shape[0], idx[0]+1), max(shape[1], idx[1]+1))
            if tensor[idx] == PASS:
                tensor.pop(idx)
        self.tensor = ExpressionTensor(tensor, shape)
        self.shape = self.tensor.shape
        Operation.__init__(self, CIRCUIT, [self.tensor])
        if len(self.shape) != 2:
            raise ValueError('Circuit operand must be a 2-D ExpressionTensor')
        # For each row of each nested sub-tensor (including the top level), 
        # determine which sub-tensor, if there are any, has the deepest nesting.
        # This will impact how we iterate over nested rows to flatten the display of a nested tensors. 
        tensor = self.tensor
        self.deepest_nested_tensor_along_row = dict() # map nested tensor (including self) to a list that indicates the deepest nested tensor per row     
        def determine_deepest_nested_tensors(tensor):            
            '''
            Determine and set the deepest nested tensor along each row of tensor,
            applying this recursively for sub-tensors, and return the depth of this tensor.
            '''
            max_depth = 1
            self.deepest_nested_tensor_along_row[tensor] = deepest_nested_tensor_along_row = []
            for row in range(tensor.shape[0]):
                deepest_nested_tensor = None
                max_depth_along_row = 1
                for col in range(tensor.shape[1]):
                    if (row, col) in tensor:
                        cell = tensor[row, col]
                        if isinstance(cell, ExpressionTensor):
                            sub_depth = determine_deepest_nested_tensors(cell)
                            max_depth_along_row = max(max_depth_along_row, sub_depth + 1)
                            if deepest_nested_tensor is None or sub_depth > max_depth_along_row:
                                deepest_nested_tensor = cell
                max_depth = max(max_depth, max_depth_along_row + 1)
                deepest_nested_tensor_along_row.append(deepest_nested_tensor)
            return max_depth
        determine_deepest_nested_tensors(self.tensor)
        #print "deepest_nested_tensors", self.deepest_nested_tensor_along_row
    
    #def substituted(self, expr_map, operation_map=None, relabel_map=None, reserved_vars=None):
    #    return Circuit(ExpressionTensor.substituted(self, expr_map, operation_map=operation_map, relabel_map=relabel_map, reserved_vars=reserved_vars))
        
    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if not 'qcircuit' in lt.packages:
            lt.packages.append('qcircuit')
        
    def generate_nested_row_indices(self):
        '''
        Generate nested row indices in order from top of the circuit to the bottom.
        Each nested row index is a list with elements corresponding to each nesting level.
        '''
        for row_indices in self._generate_nested_row_indices(self.tensor):
            yield row_indices

    def _generate_nested_row_indices(self, circuit_tensor):
        '''
        Generate nested row indices in order from top to bottom for a particular nested sub-tensor.
        Each nested row index is a list with elements corresponding to each nesting level.
        '''
        for cur_level_row, deepest_tensor_along_row in enumerate(self.deepest_nested_tensor_along_row[circuit_tensor]):
            if deepest_tensor_along_row is None: 
                yield [cur_level_row]
            else:
                for sub_nested_row in self._generate_nested_row_indices(deepest_tensor_along_row):
                    yield [cur_level_row] + sub_nested_row

    def generate_circuit_elements_along_row(self, nested_row_idx):
        '''
        Generate the circuit elements, as (level, circuit, row, column) tuples, along a particular
        nested row (as generated by generate_nested_row_indices).
        '''
        for circuit_elem in Circuit._GenerateCircuitElementsAlongRow(self.tensor, nested_row_idx, 0):
            yield circuit_elem
    
    @staticmethod
    def _GenerateCircuitElementsAlongRow(circuit_tensor, nested_row_idx, level):
        '''
        Generate the circuit elements, as (level, circuit, row, column) tuples, along a particular
        nested row (as generated by generate_nested_row_indices) at a particular nesting level.
        '''
        from .common import WIRE_UP, WIRE_DN
        row = nested_row_idx[level]
        for column in range(circuit_tensor.shape[1]):
            if (row, column) in circuit_tensor:
                cell = circuit_tensor[row, column]
                if isinstance(cell, ExpressionTensor):
                    # nested Tensor
                    for circuit_elem in Circuit._GenerateCircuitElementsAlongRow(cell, nested_row_idx, level+1):
                        yield circuit_elem
                if isinstance(cell, Output) or cell == WIRE_UP or cell == WIRE_DN:
                    yield level, circuit_tensor, row, column
                    break # nothing after the output or when the wire goes up/down (won't work if starting a new wire -- needs work)
            yield level, circuit_tensor, row, column

    def number_of_nested_rows(self, circuit_tensor, row):
        '''
        Returns the number of rows, including nested rows, spanned by a given row of a circuit_tensor
        (which may be a nested tensor).
        '''
        deepest_tensor_along_row = self.deepest_nested_tensor_along_row[circuit_tensor][row]
        if deepest_tensor_along_row is None: return 1
        return sum(self.number_of_nested_rows(deepest_tensor_along_row, sub_row) for sub_row in range(deepest_tensor_along_row.shape[0]))
    
    @staticmethod
    def _NearestTarget(circuit_tensor, row, column, direction):
        '''
        Report the vertical distance between (row, column) and
        the nearest Target in the given direction (direction < 0 for up
        and direction > 0 for down).  Raise an exception if there is
        anything in between (row, column) and the Target.
        '''
        r = row + direction
        while not (r, column) in circuit_tensor:
            r += direction
            if r < 0 or r >= circuit_tensor.shape[1]:
                raise QuantumCircuitException('Control with no target at (%d, %d)'%(row, column))                
        #if not isinstance(self.operands[r, column], Target):
        #    raise QuantumCircuitException('There must be no non-identity gate between a control and target')
        return r - row
                    
    def formatted(self, format_type, fence=False):
        return ''.join(self.formatter(format_type, fence))
    
    def formatter(self, format_type, fence=False):
        from .common import CTRL_UP, CTRL_DN, CTRL_UPDN, WIRE_UP, WIRE_DN, WIRE_LINK
        if format_type == LATEX:
            if fence: yield r'\left[' + '\n'
            yield r'\begin{array}{cc}' + '\n'
            yield r'\Qcircuit @C=1em @R=.7em {' # + '\n'
            for nested_row_idx in self.generate_nested_row_indices():
                #print "nested_row_idx", nested_row_idx
                if sum(nested_row_idx) > 0: yield r' \\ ' # previous row has ended
                for level, circuit_tensor, row, column in self.generate_circuit_elements_along_row(nested_row_idx):
                    if not (row, column) in circuit_tensor:
                        yield r' & \qw' # identity gate is a quantum wire
                    else:
                        elem = circuit_tensor[row, column]
                        if level < len(nested_row_idx)-1:
                            # we have a multigate
                            if sum(nested_row_idx[level:]) == 0:
                                # we are at the top of the multigate
                                num_multi_gate_rows = self.number_of_nested_rows(circuit_tensor, row)
                                yield r' & \multigate{' + str(num_multi_gate_rows-1) + '}{' + elem.formatted(format_type, False) + '}'
                            else:
                                # below the top of the multigate, use ghost
                                yield r' & \ghost{' + elem.formatted(format_type, False) + '}'
                        elif elem == WIRE_LINK:
                            yield r' & \qw' # junction, but the instruction here just needs to continue the horizontal wire
                        elif elem == CTRL_UP:
                            yield r' & \ctrl{' + str(Circuit._NearestTarget(circuit_tensor, row, column, -1)) + '}'
                        elif elem == CTRL_DN:
                            yield r' & \ctrl{' + str(Circuit._NearestTarget(circuit_tensor, row, column, 1)) + '}'
                        elif elem == WIRE_UP:
                            yield r' & \qwx[' + str(Circuit._NearestTarget(circuit_tensor, row, column, -1)) + '] \qw'
                        elif elem == WIRE_DN:
                            yield r' & \qwx[' + str(Circuit._NearestTarget(circuit_tensor, row, column, 1)) + '] \qw'
                        elif elem == CTRL_UPDN:
                            yield r' & \ctrl{' + str(Circuit._NearestTarget(circuit_tensor, row, column, -1)) + '}'
                            yield r' \qwx[' + str(Circuit._NearestTarget(circuit_tensor, row, column, 1)) + ']'
                        elif elem == TARGET:
                            yield r' & ' + elem.formatted(format_type, False)
                        else:
                            yield r' & ' + elem.formatted(format_type, False)
            yield '} & ~ \n'
            yield r'\end{array}'
            if fence: yield '\n' + r'\right]'
        else:
            yield Operation.formatted(self, format_type, fence)
    
CIRCUIT = Literal(pkg, 'CIRCUIT', operation_maker = lambda operands : Circuit(operands[0]))

"""                
class ForallWithImplicitIdentities(Forall):
    '''
    A Forall operation for expression involving quantum circuits
    may have Multi_variables that implicitly represent identity
    gates that are fully determined by the width of the circuit.
    By using this special kind of Forall, such Multi_variables are not
    explicitly shown as an instance variable when formatted in LATEX
    (and are not shown in the circuit).  Furthermore, they are
    instantiated automatically via an overridden "instantiate"
    method.
    '''
    
    def __init__(self, instance_vars, instance_expr, conditions=None):
        '''
        Create a special Forall expression with ImplicitIdentities as one or
        more of the instance_vars.  Adds appropriate conditions that restrict
        these to be instantiated as one or more identities.
        '''
        Forall.__init__(self, instance_vars, instance_expr, conditions=ForallWithImplicitIdentities._with_implicit_conditions(instance_vars, conditions))
        # Extract the ImplicitIdentities
        self.implicit_identities = {var for var in instance_vars if isinstance(var, ImplicitIdentities)}
        # Extract the conditions involving ImplicitIdentities
        self.implicit_conditions = {condition for condition in self.condition if not condition.free_vars().isdisjoint(self.implicit_identities)}
    
    @staticmethod
    def _with_implicit_conditions(instance_vars, conditions):
        conditions = [] if conditions is None else list(conditions)
        for var in instance_vars:
            if isinstance(var, ImplicitIdentities):
                conditions.append(are_identities(var))
        return conditions
    
    def implicit_instance_vars(self, format_type):
        '''
        ImplicitIdentities are implicit instance variables.
        '''
        if format_type == LATEX: return Forall.implicit_instance_vars(self, format_type, overridden_implicit_vars=self.implicit_identities)
        else: return Forall.implicit_instance_vars(self, format_type)

    def implicit_conditions(self, format_type):
        '''
        Conditions of ImplicitIdentities are implicit.
        '''
        if format_type == LATEX: return self.implicit_conditions
        else: return Forall.implicit_conditions(self, format_type)
    
    def instantiate(self, sub_map=None, condition_as_hypothesis=False):
        '''
        Automatically sets the ImplicitIdentities if the other instantiations
        cause the width of the quantum circuit to be determined.
        '''
        subbed_expr = self.instance_expr.substituted(sub_map)
        def fix_implicit_identity_widths(expr):
            if not isinstance(expr, Circuit):
                if isinstance(expr, ExpressionList):
                    for subexpr in expr:
                        fix_implicit_identity_widths(subexpr) # recurse over an ExpressionList
                if isinstance(expr, Operation):
                    fix_implicit_identity_widths(expr.etc_expr) # recursively search for Circuit subexpression
                    fix_implicit_identity_widths(expr.operator) # what the heck, try all the sub expressions
                elif isinstance(expr, Lambda):
                    fix_implicit_identity_widths(expr.expression)
                    fix_implicit_identity_widths(expr.domain_condition)
            else:
                if expr.has_fixed_width():
                    # A Circuit subexpression with a fixed width
                    # The width is determined, set the implicit identities as appriate
                    width = expr.width
                    for column in expr.columns:
                        for gate in column.gates:
                            if isinstance(gate, ImplicitIdentities):
                                sub_map[gate] = [I]*(width-column.min_nrows+1)
        fix_implicit_identity_widths(subbed_expr)
        return Forall.instantiate(self, sub_map)
"""

class QuantumCircuitException():
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg
    
""" 
class Gates(Operation):
    '''
    Represents a column of gate operations in parallel on one or more qubits.
    '''
    
    def __init__(self, *gates):
        Operation.__init__(self, GATE, gates)
        self.gates = gates = self.etc_expr
        self.gate_min_widths = [gate.size if hasattr(gate, 'width') else 1 for gate in gates]
        self.min_nrows = sum(self.gate_min_widths)
        self.multivar_rows = {row for row, gate in enumerate(gates) if isinstance(gate, Multi_variable)}        
        num_multivars = len(self.multivar_rows)
        # a row may only be expandable if it is the only Multi_variable of the column
        self.expandable = (num_multivars == 1)
        self.expandable_row = list(self.multivar_rows)[0] if self.expandable else None
        self.gate_by_minrow = [gate for gate, min_width in zip(self.gates, self.gate_min_widths) for _ in xrange(min_width)]
        self.expandable_gate = self.gate_by_minrow[self.expandable_row] if self.expandable_row is not None else None

    def contains_type(self, gate_type):
        '''
        Return True iff these Gates contain a a gate of the given type (class).
        '''
        for gate in self.gates:
            if isinstance(gate, gate_type):
                return True
        return False
    
    def gate_and_type(self, circuit, row):
        multivar_width = circuit.nrows - self.min_nrows + 1 # there may not be a multi-variable, that's ok
        assert multivar_width > 0, 'Should have been prevented by making the circuit nrows be the maximum of column min_nrows'
        if multivar_width > 1 and row >= self.expandable_row:
            if row < self.multivar_row+multivar_width:
                # row is within the multi-variable
                if isinstance(self.expandable_gate, ImplicitIdentities):
                    return self.expandable_gate, 'qw'
                #r'\qw {\ar @{~} [0,-1]} {\ar @{~} [0,1]}' # special case of implicit identities: squigglies
                if row == self.multivar_row: 
                    # row is at beginning of multi-variable gate
                    return self.expandable_gate, 'multigate{' + str(multivar_width-1) + '}' 
                else: return self.expandable_gate, 'ghost' # row past the multi-variable gate start
            else:
                idx = row-multivar_width+1 # row is past the mult-variable
        else:
            idx = row
        gate = self.gate_by_minrow[idx]
        if isinstance(gate, ImplicitIdentities):
            return gate, 'qw'
        if gate == CTRL_DN or gate == CTRL_UP:
            direction = 1 if gate == CTRL_DN else -1
            target_idx = idx+direction
            while self.gate_by_minrow[target_idx] == I or isinstance(self.gate_by_minrow[target_idx], ImplicitIdentities):
                target_idx += direction
            target = self.get_by_minrow[target_idx]
            assert set([gate, target]) == set([CTRL_DN, CTRL_UP]) or isinstance(target, Target), "There may only be identities between a control and target"
            if gate == CTRL_DN and self.gate_by_minrow[target_idx] == CTRL_UP:
                return gate, 'control' # one end of a CPhase with control at either end (equivalent, but not represented the same as, a controlled-Z)
            else:
                return gate, 'ctrl{' + str(target_idx - idx) + '}'
        if hasattr(gate, 'width') and gate.width > 1:
            if idx > 0 and self.gate_by_minrow[idx-1] == gate:
                return gate, 'ghost' 
            else: return gate, 'multigate{' + str(gate.width-1) + '}'
        elif gate == I: return gate, '\qw' # Identity is just a quantum wire
        else: return gate, 'gate'
         
    def formatted(self, format_type, fence=False, circuit=None, row=None, column=None, multivar_row=False):
        if format_type == LATEX:
            if row is None:
                # present the whole -- as if it were a circuit with one column
                return Circuit([self]).formatted(format_type, fence)
            else:
                gate, gate_type = self.gate_and_type(circuit, row)
                if multivar_row: 
                    if column == 0: gate_type = gate_type + 'NoIn' # No incoming wires for a first-column multi-variable
                    else: gate_type = gate_type + 's' # a multi-variable gate with a squiggly wire
                if gate_type[:4] == 'gate' or gate_type[:9] == 'multigate' or gate_type[:5] == 'ghost':
                    # for these gate types, we need that gate name included in the latex
                    return ' \\' + gate_type + '{' + gate.formatted(format_type, False) + '}'
                else:
                    return ' \\' + gate_type # e.g., \qw, \control, \ctrl{#}
        else:
            return Operation.formatted(self, format_type, fence)
        
Operation.register_operation(GATE, lambda operands : Gates(*operands))

                
class Gate(Gates):
    '''
    Represents a single gate operation as a special case of a column of gates.
    '''
    
    def __init__(self, gate):
        Gates.__init__(self, [gate])
        

class Circuit(Operation):
    '''
    Represents a quantum circuit as a sequence of parallel gate operations (Gates)
    in series -- i.e., a 2-D circuit.
    '''
    
    def __init__(self, *gate_sequence):
        Operation.__init__(self, CIRCUIT, gate_sequence)
        self.columns = gate_sequence
        self.depth = len(gate_sequence)
        assert self.depth > 0, 'Quantum circuit must not be empty'
        # check that all of the fixed columns have the same width
        widths = [column.min_nrows for column in self.columns if not isinstance(column, Multi_variable) and not column.contains_type(Multi_variable)]
        if len(widths) > 0:
            assert widths.count(widths[0]) == len(widths), 'All fixed-width columns must have the same width in a quantum circuit'
            self.width = widths[0] # has a fixed width
        # Multi_variables expand to fill to the maximum of the # of rows
        self.nrows = max([1 if isinstance(column, Multi_variable) else column.min_nrows for column in self.columns]) 
        self.multivar_rows = {row for row in xrange(self.nrows) if all(row in column.multivar_rows for column in self.columns if isinstance(column, Gates))}
    
    def has_fixed_width(self):
        return hasattr(self, 'width')

    def formatted(self, format_type, fence=False):
        if format_type == LATEX:
            out_str = '\n'
            if fence: out_str += r'\left['
            out_str += r'\begin{array}{c}' + '\n' + r'\Qcircuit @C=1em @R=.7em {'
            for row in xrange(self.nrows):
                if row > 0: out_str += r'\\' + '\n'
                for k, column in enumerate(self.columns):
                    if isinstance(column, Multi_variable):
                        postfix = 'NoIn' if k == 0 else ''
                        if row in self.multivar_rows and k > 0: postfix = 's'
                        if self.nrows == 1:
                            out_str += r'& \gate' + postfix # A multi-variable column on just one row
                        else:
                            out_str += '& ' + (r'\multigate' + postfix + '{' + str(self.nrows-1) + '}' if row == 0 else r'\ghost' + postfix)
                        out_str += '{' + column.formatted(format_type, fence) + '} '
                        # Draw a dotted box around Multi_variable columns to distinguish them from a Gates with a solo Multi_variable.
                        #out_str += r'\gategroup{1}{' + str(k+1) + '}{'+ str(self.nrows) + '}{' + str(k+2) + '}{.}{.5em}'
                    else:
                        out_str += '&' + column.formatted(LATEX, circuit=self, row=row, column=k, multivar_row=(row in self.multivar_rows))
            out_str += '}\n' + r'\end{array}' + '\n'
            if fence: out_str += r'\right]'
            return out_str
        else:
            return Operation.formatted(self, format_type, fence)
        
    def control_reversal(self, row, col):
        '''
        Given the row and column (zero-based) of a control operation of this quantum circuit,
        derive and return an equivalence with this circuit on the left and a
        circuit with an intelligently reversed control on the right.
        '''
        column = self.columns[col]
        control_type = column.gates[row]
        assert control_type == CTRL_DN or control_type == CTRL_UP
        direction = 1 if control_type == CTRL_DN else -1
        target_row = row + direction
        while column.gates[target_row] == I or isinstance(column.gates[target_row], ImplicitIdentities):
            target_row += direction
        multi_a_val = self.columns[:col]
        multi_c_val = self.columns[col+1:]
        multi_b_val = column.gates[:min(row, target_row)]
        multi_d_val = column.gates[max(row, target_row):]
        target = column.gates[target_row]
        if target == Z and control_type == CTRL_DN:
            return circuit.reverse_cz_dn.instantiate({Aetc:multi_a_val, multi_b:multi_b_val, Cetc:multi_c_val, multi_d:multi_d_val})
        elif target == Z and control_type == CTRL_UP:
            return circuit.reverse_cz_up.instantiate({Aetc:multi_a_val, multi_b:multi_b_val, Cetc:multi_c_val, multi_d:multi_d_val})
        elif target == X and control_type == CTRL_DN:
            return circuit.reverse_cnot_dn_to_up.instantiate({Aetc:multi_a_val, multi_b:multi_b_val, Cetc:multi_c_val, multi_d:multi_d_val})
        elif target == X and control_type == CTRL_UP:
            return circuit.reverse_cnot_up_to_dn.instantiate({Aetc:multi_a_val, multi_b:multi_b_val, Cetc:multi_c_val, multi_d:multi_d_val})
        

Operation.register_operation(CIRCUIT, lambda operands : Circuit(*operands))


class ForallWithImplicitIdentities(Forall):
    '''
    A Forall operation for expression involving quantum circuits
    may have Multi_variables that implicitly represent identity
    gates that are fully determined by the width of the circuit.
    By using this special kind of Forall, such Multi_variables are not
    explicitly shown as an instance variable when formatted in LATEX
    (and are not shown in the circuit).  Furthermore, they are
    instantiated automatically via an overridden "instantiate"
    method.
    '''
    
    def __init__(self, instance_vars, instance_expr, conditions=None):
        '''
        Create a special Forall expression with ImplicitIdentities as one or
        more of the instance_vars.  Adds appropriate conditions that restrict
        these to be instantiated as one or more identities.
        '''
        Forall.__init__(self, instance_vars, instance_expr, conditions=ForallWithImplicitIdentities._with_implicit_conditions(instance_vars, conditions))
        # Extract the ImplicitIdentities
        self.implicit_identities = {var for var in instance_vars if isinstance(var, ImplicitIdentities)}
        # Extract the conditions involving ImplicitIdentities
        self.implicit_conditions = {condition for condition in self.condition if not condition.free_vars().isdisjoint(self.implicit_identities)}
    
    @staticmethod
    def _with_implicit_conditions(instance_vars, conditions):
        conditions = [] if conditions is None else list(conditions)
        for var in instance_vars:
            if isinstance(var, ImplicitIdentities):
                conditions.append(are_identities(var))
        return conditions
    
    def implicit_instance_vars(self, format_type):
        '''
        ImplicitIdentities are implicit instance variables.
        '''
        if format_type == LATEX: return Forall.implicit_instance_vars(self, format_type, overridden_implicit_vars=self.implicit_identities)
        else: return Forall.implicit_instance_vars(self, format_type)

    def implicit_conditions(self, format_type):
        '''
        Conditions of ImplicitIdentities are implicit.
        '''
        if format_type == LATEX: return self.implicit_conditions
        else: return Forall.implicit_conditions(self, format_type)
    
    def instantiate(self, sub_map=None, condition_as_hypothesis=False):
        '''
        Automatically sets the ImplicitIdentities if the other instantiations
        cause the width of the quantum circuit to be determined.
        '''
        subbed_expr = self.instance_expr.substituted(sub_map)
        def fix_implicit_identity_widths(expr):
            if not isinstance(expr, Circuit):
                if isinstance(expr, ExpressionList):
                    for subexpr in expr:
                        fix_implicit_identity_widths(subexpr) # recurse over an ExpressionList
                if isinstance(expr, Operation):
                    fix_implicit_identity_widths(expr.etc_expr) # recursively search for Circuit subexpression
                    fix_implicit_identity_widths(expr.operator) # what the heck, try all the sub expressions
                elif isinstance(expr, Lambda):
                    fix_implicit_identity_widths(expr.expression)
                    fix_implicit_identity_widths(expr.domain_condition)
            else:
                if expr.has_fixed_width():
                    # A Circuit subexpression with a fixed width
                    # The width is determined, set the implicit identities as appriate
                    width = expr.width
                    for column in expr.columns:
                        for gate in column.gates:
                            if isinstance(gate, ImplicitIdentities):
                                sub_map[gate] = [I]*(width-column.min_nrows+1)
        fix_implicit_identity_widths(subbed_expr)
        return Forall.instantiate(self, sub_map)
            
"""            
        

        
