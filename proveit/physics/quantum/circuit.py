import sys
from proveit.statement import Literals, Operation, Variable, MultiVariable, Lambda, ExpressionList, STRING, LATEX
from proveit.context import Context
from proveit.basiclogic import Forall, In, List, Equals
from proveit.computer_science.regular_expressions import KleeneRepetition
from Carbon import ControlAccessor

# quantum circuit literals
literals = Literals()
GATE = literals.add('GATE')
CIRCUIT = literals.add('CIRCUIT')
I = literals.add('I') # Single qubit identity
X = literals.add('X') # Pauli-X
Y = literals.add('Y') # Pauli-Y
Z = literals.add('Z') # Pauli-Z
H = literals.add('H') # Hadamard
CTRL_UP = literals.add('CTRL_UP')
CTRL_DN = literals.add('CTRL_DN')
CTRL_UPDN = literals.add('CTRL_UPDN')

# A BARRIER is required to separate independent gates that operate in parallel
# and are adjacent in a quantum circuit (e.g., no controlled gate between them):
BARRIER = literals.add('BARRIER', {STRING:'|', LATEX:'|'})

class ImplicitIdentities(MultiVariable):
    '''
    ImplicitIdentities are used in quantum circuits where they must be
    filled in with one or more identities as determined by the width of
    the circuit (which isn't established until MultiVariables are specialized).
    See ForallWithImplicitIdentities.
    '''
    
    def __init__(self, name, formatMap = None):
        MultiVariable.__init__(self, name, formatMap)
    
def areIdentities(gates):
    '''
    Returns the expression that the set of gates, as a List, are in the set of repeating identities.
    In other words, an expression that is true if all of the gates are identity gates.
    '''
    return In(List(gates), KleeneRepetition(I))

# some Variable labels
multiA = MultiVariable('A')
multiB = MultiVariable('B')
multiB1 = MultiVariable('B1')
multiB2 = MultiVariable('B2')
multiB3 = MultiVariable('B3')
multiC = MultiVariable('C')
multiC1 = MultiVariable('C1')
multiC2 = MultiVariable('C2')
multiC3 = MultiVariable('C3')
multiD = MultiVariable('D')
# for implicit identity gates
Is = ImplicitIdentities('I') 
IsB = ImplicitIdentities('IB') 
IsC = ImplicitIdentities('IC') 

def _defineAxioms():
    return None # For now, we're just asserting the theorems without proof.

def _defineTheorems():
    _firstTheorem = \
    identityCollapse = ForallWithImplicitIdentities([multiA, multiB, Is], Equals(Circuit(multiA, Gates(Is), multiB), Circuit(multiA, multiB)))
    reverseCzDn = ForallWithImplicitIdentities([multiA, multiB, multiC, multiD, Is], Equals(Circuit(multiA, Gates(multiB, Z, Is, CTRL_UP, multiC), multiD), 
                                                                                            Circuit(multiA, Gates(multiB, CTRL_DN, Is, Z, multiC), multiD)))
    reverseCzUp = ForallWithImplicitIdentities([multiA, multiB, multiC, multiD, Is], Equals(Circuit(multiA, Gates(multiB, CTRL_DN, Is, Z, multiC), multiD), 
                                                                                            Circuit(multiA, Gates(multiB, Z, Is, CTRL_UP, multiC), multiD)))
    reverseCnotDnToUp = ForallWithImplicitIdentities([multiA, multiB, multiC, multiD, Is], 
                                                     Equals(Circuit(multiA, Gates(multiB, CTRL_DN, Is, X, multiC), multiD), 
                                                            Circuit(multiA, Gates(IsB, H, Is, H, IsC), Gates(multiB, X, Is, CTRL_UP, multiC2), Gates(IsB, H, Is, H, IsC), multiD)))
    reverseCnotUpToDn = ForallWithImplicitIdentities([multiA, multiB, multiC, multiD, Is], 
                                                     Equals(Circuit(multiA, Gates(multiB, X, Is, CTRL_UP, multiC), multiD), 
                                                            Circuit(multiA, Gates(IsB, H, Is, H, IsC), Gates(multiB, CTRL_DN, Is, X, multiC2), Gates(IsB, H, Is, H, IsC), multiD)))
    return _firstTheorem, locals()

circuit = Context(sys.modules[__name__], literals, _defineAxioms, _defineTheorems)
        
class Gates(Operation):
    '''
    Represents a column of gate operations in parallel on one or more qubits.
    '''
    
    def __init__(self, *gates):
        Operation.__init__(self, GATE, gates)
        self.gates = gates = self.operand
        self.gate_min_widths = [gate.size if hasattr(gate, 'width') else 1 for gate in gates]
        self.min_nrows = sum(self.gate_min_widths)
        self.multivar_rows = {row for row, gate in enumerate(gates) if isinstance(gate, MultiVariable)}        
        num_multivars = len(self.multivar_rows)
        # a row may only be expandable if it is the only MultiVariable of the column
        self.expandable = (num_multivars == 1)
        self.expandable_row = list(self.multivar_rows)[0] if self.expandable else None
        self.gate_by_minrow = [gate for gate, min_width in zip(self.gates, self.gate_min_widths) for _ in xrange(min_width)]
        self.expandable_gate = self.gate_by_minrow[self.expandable_row] if self.expandable_row is not None else None

    def containsType(self, gate_type):
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
         
    def formatted(self, formatType, fenced=False, circuit=None, row=None, column=None, multivar_row=False):
        if formatType == LATEX:
            if row is None:
                # present the whole -- as if it were a circuit with one column
                return Circuit([self]).formatted(formatType, fenced)
            else:
                gate, gate_type = self.gate_and_type(circuit, row)
                if multivar_row: 
                    if column == 0: gate_type = gate_type + 'NoIn' # No incoming wires for a first-column multi-variable
                    else: gate_type = gate_type + 's' # a multi-variable gate with a squiggly wire
                if gate_type[:4] == 'gate' or gate_type[:9] == 'multigate' or gate_type[:5] == 'ghost':
                    # for these gate types, we need that gate name included in the latex
                    return ' \\' + gate_type + '{' + gate.formatted(formatType, False) + '}'
                else:
                    return ' \\' + gate_type # e.g., \qw, \control, \ctrl{#}
        else:
            return Operation.formatted(self, formatType, fenced)
        
Operation.registerOperation(GATE, lambda operands : Gates(*operands))

                
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
        widths = [column.min_nrows for column in self.columns if not isinstance(column, MultiVariable) and not column.containsType(MultiVariable)]
        if len(widths) > 0:
            assert widths.count(widths[0]) == len(widths), 'All fixed-width columns must have the same width in a quantum circuit'
            self.width = widths[0] # has a fixed width
        # MultiVariables expand to fill to the maximum of the # of rows
        self.nrows = max([1 if isinstance(column, MultiVariable) else column.min_nrows for column in self.columns]) 
        self.multivar_rows = {row for row in xrange(self.nrows) if all(row in column.multivar_rows for column in self.columns if isinstance(column, Gates))}
    
    def hasFixedWidth(self):
        return hasattr(self, 'width')

    def formatted(self, formatType, fenced=False):
        if formatType == LATEX:
            outStr = '\n'
            if fenced: outStr += r'\left['
            outStr += r'\begin{array}{c}' + '\n' + r'\Qcircuit @C=1em @R=.7em {'
            for row in xrange(self.nrows):
                if row > 0: outStr += r'\\' + '\n'
                for k, column in enumerate(self.columns):
                    if isinstance(column, MultiVariable):
                        postfix = 'NoIn' if k == 0 else ''
                        if row in self.multivar_rows and k > 0: postfix = 's'
                        if self.nrows == 1:
                            outStr += r'& \gate' + postfix # A multi-variable column on just one row
                        else:
                            outStr += '& ' + (r'\multigate' + postfix + '{' + str(self.nrows-1) + '}' if row == 0 else r'\ghost' + postfix)
                        outStr += '{' + column.formatted(formatType, fenced) + '} '
                        # Draw a dotted box around MultiVariable columns to distinguish them from a Gates with a solo MultiVariable.
                        #outStr += r'\gategroup{1}{' + str(k+1) + '}{'+ str(self.nrows) + '}{' + str(k+2) + '}{.}{.5em}'
                    else:
                        outStr += '&' + column.formatted(LATEX, circuit=self, row=row, column=k, multivar_row=(row in self.multivar_rows))
            outStr += '}\n' + r'\end{array}' + '\n'
            if fenced: outStr += r'\right]'
            return outStr
        else:
            return Operation.formatted(self, formatType, fenced)
        
    def controlReversal(self, row, col):
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
        multiA_val = self.columns[:col]
        multiC_val = self.columns[col+1:]
        multiB_val = column.gates[:min(row, target_row)]
        multiD_val = column.gates[max(row, target_row):]
        target = column.gates[target_row]
        if target == Z and control_type == CTRL_DN:
            return circuit.reverseCzDn.specialize({multiA:multiA_val, multiB:multiB_val, multiC:multiC_val, multiD:multiD_val})
        elif target == Z and control_type == CTRL_UP:
            return circuit.reverseCzUp.specialize({multiA:multiA_val, multiB:multiB_val, multiC:multiC_val, multiD:multiD_val})
        elif target == X and control_type == CTRL_DN:
            return circuit.reverseCnotDnToUp.specialize({multiA:multiA_val, multiB:multiB_val, multiC:multiC_val, multiD:multiD_val})
        elif target == X and control_type == CTRL_UP:
            return circuit.reverseCnotUpToDn.specialize({multiA:multiA_val, multiB:multiB_val, multiC:multiC_val, multiD:multiD_val})
        

Operation.registerOperation(CIRCUIT, lambda operands : Circuit(*operands))


class ForallWithImplicitIdentities(Forall):
    '''
    A Forall operation for expression involving quantum circuits
    may have MultiVariables that implicitly represent identity
    gates that are fully determined by the width of the circuit.
    By using this special kind of Forall, such MultiVariables are not
    explicitly shown as an instance variable when formatted in LATEX
    (and are not shown in the circuit).  Furthermore, they are
    specialized automatically via an overridden "specialize"
    method.
    '''
    
    def __init__(self, instanceVars, instanceExpression, conditions=None):
        '''
        Create a special Forall expression with ImplicitIdentities as one or
        more of the instanceVars.  Adds appropriate conditions that restrict
        these to be specialized as one or more identities.
        '''
        Forall.__init__(self, instanceVars, instanceExpression, conditions=ForallWithImplicitIdentities._with_implicit_conditions(instanceVars, conditions))
        # Extract the ImplicitIdentities
        self.implicit_identities = {var for var in instanceVars if isinstance(var, ImplicitIdentities)}
        # Extract the conditions involving ImplicitIdentities
        self.implicit_conditions = {condition for condition in self.condition if not condition.freeVars().isdisjoint(self.implicit_identities)}
    
    @staticmethod
    def _with_implicit_conditions(instanceVars, conditions):
        conditions = [] if conditions is None else list(conditions)
        for var in instanceVars:
            if isinstance(var, ImplicitIdentities):
                conditions.append(areIdentities(var))
        return conditions
    
    def implicitInstanceVars(self, formatType):
        '''
        ImplicitIdentities are implicit instance variables.
        '''
        if formatType == LATEX: return Forall.implicitInstanceVars(self, formatType, overriddenImplicitVars=self.implicit_identities)
        else: return Forall.implicitInstanceVars(self, formatType)

    def implicitConditions(self, formatType):
        '''
        Conditions of ImplicitIdentities are implicit.
        '''
        if formatType == LATEX: return self.implicit_conditions
        else: return Forall.implicitConditions(self, formatType)
    
    def specialize(self, subMap=None, conditionAsHypothesis=False):
        '''
        Automatically sets the ImplicitIdentities if the other specializations
        cause the width of the quantum circuit to be determined.
        '''
        subbed_expr = self.instanceExpression.substituted(subMap)
        def fixImplicitIdentityWidths(expr):
            if not isinstance(expr, Circuit):
                if isinstance(expr, ExpressionList):
                    for subexpr in expr:
                        fixImplicitIdentityWidths(subexpr) # recurse over an ExpressionList
                if isinstance(expr, Operation):
                    fixImplicitIdentityWidths(expr.operand) # recursively search for Circuit subexpression
                    fixImplicitIdentityWidths(expr.operator) # what the heck, try all the sub expressions
                elif isinstance(expr, Lambda):
                    fixImplicitIdentityWidths(expr.expression)
                    fixImplicitIdentityWidths(expr.domainCondition)
            else:
                if expr.hasFixedWidth():
                    # A Circuit subexpression with a fixed width
                    # The width is determined, set the implicit identities as appriate
                    width = expr.width
                    for column in expr.columns:
                        for gate in column.gates:
                            if isinstance(gate, ImplicitIdentities):
                                subMap[gate] = [I]*(width-column.min_nrows+1)
        fixImplicitIdentityWidths(subbed_expr)
        return Forall.specialize(self, subMap)
            
            
        
        
        