import sys
from proveit import Lambda, Literal, Operation
from proveit._core_.expression.composite import ExprArray, ExprTuple, ExprRange
# not clear yet what to substitute for ExpressionTensor -- perhaps ExprArray
# and Block is not being used in the active code
# from proveit.multiExpression import ExpressionTensor, Block
# from proveit.logic import Forall, Equals, InSet
# from proveit.computer_science.regular_expressions import KleeneRepetition

pkg = __package__ # can probably delete later

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
    the circuit (which isn't established until Blocks are specialized).
    See ForallWithImplicitIdentities.
    '''
    def __init__(self, name, formatMap = None):
        Block.__init__(self, name, formatMap)
"""

"""    
def areIdentities(gates):
    '''
    Returns the expression that the set of gates, as a List, are in the set of repeating identities.
    In other words, an expression that is true if all of the gates are identity gates.
    '''
    return In(List(gates), KleeneRepetition(I))



def _defineAxioms():
    return None # For now, we're just asserting the theorems without proof.

def _defineTheorems():
    _firstTheorem = \
    identityCollapse = ForallWithImplicitIdentities([Aetc, multiB, Is], Equals(Circuit(Aetc, Gates(Is), multiB), Circuit(Aetc, multiB)))
    reverseCzDn = ForallWithImplicitIdentities([Aetc, multiB, Cetc, multiD, Is], Equals(Circuit(Aetc, Gates(multiB, Target(Z), Is, CTRL_UP, Cetc), multiD), 
                                                                                            Circuit(Aetc, Gates(multiB, CTRL_DN, Is, Target(Z), Cetc), multiD)))
    reverseCzUp = ForallWithImplicitIdentities([Aetc, multiB, Cetc, multiD, Is], Equals(Circuit(Aetc, Gates(multiB, CTRL_DN, Is, Target(Z), Cetc), multiD), 
                                                                                            Circuit(Aetc, Gates(multiB, Target(Z), Is, CTRL_UP, Cetc), multiD)))
    reverseCnotDnToUp = ForallWithImplicitIdentities([Aetc, multiB, Cetc, multiD, Is, IsB, IsC], 
                                                     Equals(Circuit(Aetc, Gates(multiB, CTRL_DN, Is, Target(X), Cetc), multiD), 
                                                            Circuit(Aetc, Gates(IsB, H, Is, H, IsC), Gates(multiB, Target(X), Is, CTRL_UP, Cetc), Gates(IsB, H, Is, H, IsC), multiD)))
    reverseCnotUpToDn = ForallWithImplicitIdentities([Aetc, multiB, Cetc, multiD, Is, IsB, IsC], 
                                                     Equals(Circuit(Aetc, Gates(multiB, Target(X), Is, CTRL_UP, Cetc), multiD), 
                                                            Circuit(Aetc, Gates(IsB, H, Is, H, IsC), Gates(multiB, CTRL_DN, Is, Target(X), Cetc), Gates(IsB, H, Is, H, IsC), multiD)))
    return _firstTheorem, locals()
"""


class Input(Operation):
    '''
    Represents an input state entering from the left-hand side of a
    circuit. Updated 1/26/2020 by wdc
    '''
    # the literal operator of the Input operation class
    _operator_ = Literal('INPUT', context=__file__)
    
    def __init__(self, state):
        '''
        Create an INPUT operation (for entering the left-hand side
        of a circuit) with the given input state.
        '''
        Operation.__init__(self, Input._operator_, state)
        self.state = state

    def formatted(self, formatType, fence=False):
        formattedState = self.state.formatted(formatType, fence=False)
        if formatType == 'latex':
            return r'\lstick{' + formattedState + r'}' 
        else:
            return Operation._formatted(self, formatType, fence=fence)


INPUT = Literal(pkg, 'INPUT')  # , operationMaker=lambda operands: Input(*operands))
# An input state (entering the left of the circuit)


class Output(Operation):
    '''
    Represents an output state exiting from the right-hand side of
    a circuit. Updated 1/26/2020 by wdc
    '''
    # the literal operator of the Output operation class
    _operator_ = Literal('OUTPUT', context=__file__)
    
    def __init__(self, state):
        '''
        Create an OUTPUT operation with the given input state.
        '''    
        Operation.__init__(self, Output._operator_, state)
        self.state = state
    
    def formatted(self, formatType, fence=False):
        formattedState = self.state.formatted(formatType, fence=False)
        if formatType == 'latex':
            return r'\rstick{' + formattedState + r'} \qw' 
        else: return Operation._formatted(self, formatType, fence)


OUTPUT = Literal(pkg, 'OUTPUT')  # , operationMaker=lambda operands: Output(*operands))
# An output state (exiting the right of the circuit)


class Gate(Operation):
    '''
    Represents a gate in a quantum circuit.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('GATE', context=__file__)
    
    def __init__(self, gate_operation):
        '''
        Create a quantum circuit gate performing the given operation.
        '''    
        Operation.__init__(self, Gate._operator_, gate_operation)
        self.gate_operation = self.operands[0]

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, formatType, **kwargs):
        formattedGateOperation = (
                self.gate_operation.formatted(formatType, fence=False))
        if formatType == 'latex':
            return r'\gate{' + formattedGateOperation + r'}'
        else:
            return Operation._formatted(self, formatType)

    # original below
    # def formatted(self, formatType, fence=false):
    #     print("Entering Gate.formatted.")                                       # for testing; delete later
    #     print("  formatType = {}".format(formatType))                           # for testing; delete later
    #     formattedGateOperation = (
    #             self.gate_operation.formatted(formatType, fence=False))
    #     if formatType == 'latex':
    #         return r'\gate{' + formattedGateOperation + r'}' 
    #     else: return Operation._formatted(self, formatType, fence)


class Target(Operation):
    '''
    Represents the target of a control.
    Updated 1/26/2020 by wdc.
    '''
    # the literal operator of the Target operation class
    _operator_ = Literal('TARGET', latexFormat=r'\targ',  context=__file__)
    
    def __init__(self, target_gate):
        '''
        Create a Target operation with the given target_gate as the type
        of the gate for the target (e.g., X for CNOT and Z for Controlled-Z).
        '''    
        Operation.__init__(self, Target._operator_, target_gate)
        self.target_gate = target_gate

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, formatType, fence=False):
        if formatType == 'latex':
            return r'\targ'
        else:
            return Operation._formatted(self, formatType)

# TARGET = Literal(pkg, 'TARGET', {STRING:'TARGET', LATEX:r'\targ'}, lambda operands : Target(*operands))

# class MultiWire(Operation):
#     '''
#     Marks a "wire" as a bundle with a number of individual wires.
#     '''
    
#     def __init__(self, number):
#         '''
#         Create a multi-wire.
#         '''    
#         Operation.__init__(self, MULTI_WIRE, number)
#         self.number = number
    
#     def formatted(self, formatType, fence=False):
#         formattedNumber = self.number.formatted(formatType, fence=False)
#         if formatType == LATEX:
#             return r'/^{' + formattedNumber + r'} \qw' 
#         else: return Operation.formatted(self, formatType, fence)

# MULTI_WIRE = Literal(pkg, 'MULTI_WIRE', operationMaker = lambda operands : MultiWire(*operands))


class Circuit(ExprArray):
    '''
    Represents a quantum circuit as a 2-D ExprArray
    '''

    def __init__(self, *expressions, styles=None):
        '''
        Initialize an ExprTuple from an iterable over Expression
        objects.
        '''
        if styles is None: styles = dict()
        if 'orientation' not in styles:
            styles['orientation'] = 'horizontal'

        ExprTuple.__init__(self, *expressions, styles=styles)

        for entry in self:
            if not isinstance(entry, ExprTuple) and not isinstance(entry, ExprRange):
                raise ValueError("Contents of an ExprArray must be wrapped in either an ExprRange or ExprTuple.")

        # check each column for same expression throughout
        self.checkRange()

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, formatType, fence=False, subFence=False, operatorOrOperators=None, implicitFirstOperator=False,
                  wrapPositions=None, orientation=None, **kwargs):
        from proveit._core_.expression.expr import Expression
        default_style = ("explicit" if formatType == 'string' else 'implicit')

        outStr = ''
        if len(self) == 0 and fence:
            # for an empty list, show the parenthesis to show something.
            return '()'

        if orientation is None:
            orientation = self.getStyle('orientation', 'horizontal')

        if formatType == 'latex':
            outStr += r'\Qcircuit @C=1em @R=.7em {' + '\n'

        formatted_sub_expressions, using_explicit_parameterization = self.getFormattedSubExpressions(formatType,
                                                                                                     orientation,
                                                                                                     default_style,
                                                                                                    operatorOrOperators)

        if orientation == "vertical":
            # up until now, the formatted_sub_expression is still
            # in the order of the horizontal orientation regardless of orientation type
            k = 1
            vert = []
            if self.getStyle('parameterization', default_style) == 'explicit':
                ex = True
            else:
                ex = False
            m = self.getColHeight(ex)
            while k <= self.getRowLength(ex):
                i = 1
                j = k
                for var in formatted_sub_expressions:
                    if i == j:
                        vert.append(var)
                        m -= 1
                        if m == 0:
                            vert.append(r' \\' + ' \n ')
                            m = self.getColHeight(ex)
                        j += self.getRowLength(ex)
                    i += 1
                k += 1
            formatted_sub_expressions = vert

        if operatorOrOperators is None:
            operatorOrOperators = ','
        elif isinstance(operatorOrOperators, Expression) and not isinstance(operatorOrOperators, ExprTuple):
            operatorOrOperators = operatorOrOperators.formatted(formatType, fence=False)
        if isinstance(operatorOrOperators, str):
            # single operator
            formatted_operator = operatorOrOperators
            if operatorOrOperators == ',':
                # e.g.: a, b, c, d
                outStr += (' ').join(formatted_sub_expressions)
            else:
                # e.g.: a + b + c + d
                outStr += (' '+formatted_operator+' ').join(formatted_sub_expressions)
        else:
            # assume all different operators
            formatted_operators = []
            for operator in operatorOrOperators:
                if isinstance(operator, ExprRange):
                    # Handle an ExprRange entry; here the "operators"
                    # are really ExprRange "checkpoints" (first, last,
                    # as well as the ExprRange body in the middle if
                    # using an 'explicit' style for 'parameterization').
                    # For the 'ellipses', we will just use a
                    # placeholder.
                    be_explicit = using_explicit_parameterization.pop(0)
                    formatted_operators += operator._formatted_checkpoints(
                        formatType, fence=False, subFence=False, ellipses='',
                        use_explicit_parameterization=be_explicit)
                else:
                    formatted_operators.append(operator.formatted(formatType, fence=False, subFence=False))
            if len(formatted_sub_expressions) == len(formatted_operators):
                # operator preceeds each operand
                if implicitFirstOperator:
                    outStr = formatted_sub_expressions[0]  # first operator is implicit
                else:
                    outStr = formatted_operators[0] + formatted_sub_expressions[0]  # no space after first operator
                outStr += ' '  # space before next operator
                outStr += ' '.join(
                    formatted_operator + ' ' + formatted_operand for formatted_operator, formatted_operand in
                    zip(formatted_operators[1:], formatted_sub_expressions[1:]))
            elif len(formatted_sub_expressions) == len(formatted_operators) + 1:
                # operator between each operand
                outStr = ' '.join(
                    formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in
                    zip(formatted_sub_expressions, formatted_operators))
                outStr += ' ' + formatted_sub_expressions[-1]
            elif len(formatted_sub_expressions) != len(formatted_operators):
                raise ValueError(
                    "May only perform ExprTuple formatting if the number of operators is equal to the number "
                    "of operands(precedes each operand) or one less (between each operand); "
                    "also, operator ranges must be in correspondence with operand ranges.")

        if formatType == 'latex':
            outStr += ' \n' + '}'
        print(outStr)
        return outStr

    def _config_latex_tool(self, lt):
        print('config latex!!')
        Operation._config_latex_tool(self, lt)
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')


# class Circuit(Operation):
#     '''
#     Represents a quantum circuit as a 2-D ExpressionTensor.
#     '''
#     def __init__(self, tensor, shape=None):
#         '''
#         Create a Circuit either with a dense tensor (list of lists ... of lists) or
#         with a dictionary mapping pairs of indices to Expression elements or blocks,
#         composing an ExpressionTensor.
#         '''
#         from .common import PASS
#         if not isinstance(tensor, dict):
#             # remove identity gates -- these are implicit
#             tensor, _ = ExpressionTensor.TensorDictFromIterables(tensor)
#         fixed_shape = (shape is not None)
#         if not fixed_shape:
#             shape = (0, 0)
#         for idx in list(tensor.keys()):
#             if len(idx) != 2:
#                 raise ValueError('Circuit operand must be a 2-D ExpressionTensor')
#             if not fixed_shape:
#                 shape = (max(shape[0], idx[0]+1), max(shape[1], idx[1]+1))
#             if tensor[idx] == PASS:
#                 tensor.pop(idx)
#         self.tensor = ExpressionTensor(tensor, shape)
#         self.shape = self.tensor.shape
#         Operation.__init__(self, CIRCUIT, [self.tensor])
#         if len(self.shape) != 2:
#             raise ValueError('Circuit operand must be a 2-D ExpressionTensor')
#         # For each row of each nested sub-tensor (including the top level), 
#         # determine which sub-tensor, if there are any, has the deepest nesting.
#         # This will impact how we iterate over nested rows to flatten the display of a nested tensors. 
#         tensor = self.tensor
#         self.deepestNestedTensorAlongRow = dict()
#           # map nested tensor (including self) to a list that indicates the deepest nested tensor per row
#         def determineDeepestNestedTensors(tensor):            
#             '''
#             Determine and set the deepest nested tensor along each row of tensor,
#             applying this recursively for sub-tensors, and return the depth of this tensor.
#             '''
#             maxDepth = 1
#             self.deepestNestedTensorAlongRow[tensor] = deepestNestedTensorAlongRow = []
#             for row in range(tensor.shape[0]):
#                 deepestNestedTensor = None
#                 maxDepthAlongRow = 1
#                 for col in range(tensor.shape[1]):
#                     if (row, col) in tensor:
#                         cell = tensor[row, col]
#                         if isinstance(cell, ExpressionTensor):
#                             subDepth = determineDeepestNestedTensors(cell)
#                             maxDepthAlongRow = max(maxDepthAlongRow, subDepth + 1)
#                             if deepestNestedTensor is None or subDepth > maxDepthAlongRow:
#                                 deepestNestedTensor = cell
#                 maxDepth = max(maxDepth, maxDepthAlongRow + 1)
#                 deepestNestedTensorAlongRow.append(deepestNestedTensor)
#             return maxDepth
#         determineDeepestNestedTensors(self.tensor)
#         #print "deepestNestedTensors", self.deepestNestedTensorAlongRow
    
#     #def substituted(self, exprMap, operationMap=None, relabelMap=None, reservedVars=None):
#     #    return Circuit(ExpressionTensor.substituted(self, exprMap, operationMap=operationMap,
#     relabelMap=relabelMap, reservedVars=reservedVars))
        
#     def _config_latex_tool(self, lt):
#         Operation._config_latex_tool(self, lt)
#         if not 'qcircuit' in lt.packages:
#             lt.packages.append('qcircuit')
        
#     def generateNestedRowIndices(self):
#         '''
#         Generate nested row indices in order from top of the circuit to the bottom.
#         Each nested row index is a list with elements corresponding to each nesting level.
#         '''
#         for rowIndices in self._generateNestedRowIndices(self.tensor):
#             yield rowIndices

#     def _generateNestedRowIndices(self, circuitTensor):
#         '''
#         Generate nested row indices in order from top to bottom for a particular nested sub-tensor.
#         Each nested row index is a list with elements corresponding to each nesting level.
#         '''
#         for curLevelRow, deepestTensorAlongRow in enumerate(self.deepestNestedTensorAlongRow[circuitTensor]):
#             if deepestTensorAlongRow is None: 
#                 yield [curLevelRow]
#             else:
#                 for subNestedRow in self._generateNestedRowIndices(deepestTensorAlongRow):
#                     yield [curLevelRow] + subNestedRow

#     def generateCircuitElementsAlongRow(self, nestedRowIdx):
#         '''
#         Generate the circuit elements, as (level, circuit, row, column) tuples, along a particular
#         nested row (as generated by generateNestedRowIndices).
#         '''
#         for circuitElem in Circuit._GenerateCircuitElementsAlongRow(self.tensor, nestedRowIdx, 0):
#             yield circuitElem
    
#     @staticmethod
#     def _GenerateCircuitElementsAlongRow(circuitTensor, nestedRowIdx, level):
#         '''
#         Generate the circuit elements, as (level, circuit, row, column) tuples, along a particular
#         nested row (as generated by generateNestedRowIndices) at a particular nesting level.
#         '''
#         from .common import WIRE_UP, WIRE_DN
#         row = nestedRowIdx[level]
#         for column in range(circuitTensor.shape[1]):
#             if (row, column) in circuitTensor:
#                 cell = circuitTensor[row, column]
#                 if isinstance(cell, ExpressionTensor):
#                     # nested Tensor
#                     for circuitElem in Circuit._GenerateCircuitElementsAlongRow(cell, nestedRowIdx, level+1):
#                         yield circuitElem
#                 if isinstance(cell, Output) or cell == WIRE_UP or cell == WIRE_DN:
#                     yield level, circuitTensor, row, column
#                     break # nothing after the output or when the wire goes up/down (won't work if starting a new wire -- needs work)
#             yield level, circuitTensor, row, column

#     def numberOfNestedRows(self, circuitTensor, row):
#         '''
#         Returns the number of rows, including nested rows, spanned by a given row of a circuitTensor
#         (which may be a nested tensor).
#         '''
#         deepestTensorAlongRow = self.deepestNestedTensorAlongRow[circuitTensor][row]
#         if deepestTensorAlongRow is None: return 1
#         return sum(self.numberOfNestedRows(deepestTensorAlongRow, subRow) for subRow in range(deepestTensorAlongRow.shape[0]))
    
#     @staticmethod
#     def _NearestTarget(circuitTensor, row, column, direction):
#         '''
#         Report the vertical distance between (row, column) and
#         the nearest Target in the given direction (direction < 0 for up
#         and direction > 0 for down).  Raise an exception if there is
#         anything in between (row, column) and the Target.
#         '''
#         r = row + direction
#         while not (r, column) in circuitTensor:
#             r += direction
#             if r < 0 or r >= circuitTensor.shape[1]:
#                 raise QuantumCircuitException('Control with no target at (%d, %d)'%(row, column))                
#         #if not isinstance(self.operands[r, column], Target):
#         #    raise QuantumCircuitException('There must be no non-identity gate between a control and target')
#         return r - row
                    
#     def formatted(self, formatType, fence=False):
#         return ''.join(self.formatter(formatType, fence))
    
#     def formatter(self, formatType, fence=False):
#         from .common import CTRL_UP, CTRL_DN, CTRL_UPDN, WIRE_UP, WIRE_DN, WIRE_LINK
#         if formatType == LATEX:
#             if fence: yield r'\left[' + '\n'
#             yield r'\begin{array}{cc}' + '\n'
#             yield r'\Qcircuit @C=1em @R=.7em {' # + '\n'
#             for nestedRowIdx in self.generateNestedRowIndices():
#                 #print "nestedRowIdx", nestedRowIdx
#                 if sum(nestedRowIdx) > 0: yield r' \\ ' # previous row has ended
#                 for level, circuitTensor, row, column in self.generateCircuitElementsAlongRow(nestedRowIdx):
#                     if not (row, column) in circuitTensor:
#                         yield r' & \qw' # identity gate is a quantum wire
#                     else:
#                         elem = circuitTensor[row, column]
#                         if level < len(nestedRowIdx)-1:
#                             # we have a multigate
#                             if sum(nestedRowIdx[level:]) == 0:
#                                 # we are at the top of the multigate
#                                 numMultiGateRows = self.numberOfNestedRows(circuitTensor, row)
#                                 yield r' & \multigate{' + str(numMultiGateRows-1) + '}{' + elem.formatted(formatType, False) + '}'
#                             else:
#                                 # below the top of the multigate, use ghost
#                                 yield r' & \ghost{' + elem.formatted(formatType, False) + '}'
#                         elif elem == WIRE_LINK:
#                             yield r' & \qw' # junction, but the instruction here just needs to continue the horizontal wire
#                         elif elem == CTRL_UP:
#                             yield r' & \ctrl{' + str(Circuit._NearestTarget(circuitTensor, row, column, -1)) + '}'
#                         elif elem == CTRL_DN:
#                             yield r' & \ctrl{' + str(Circuit._NearestTarget(circuitTensor, row, column, 1)) + '}'
#                         elif elem == WIRE_UP:
#                             yield r' & \qwx[' + str(Circuit._NearestTarget(circuitTensor, row, column, -1)) + '] \qw'
#                         elif elem == WIRE_DN:
#                             yield r' & \qwx[' + str(Circuit._NearestTarget(circuitTensor, row, column, 1)) + '] \qw'
#                         elif elem == CTRL_UPDN:
#                             yield r' & \ctrl{' + str(Circuit._NearestTarget(circuitTensor, row, column, -1)) + '}'
#                             yield r' \qwx[' + str(Circuit._NearestTarget(circuitTensor, row, column, 1)) + ']'
#                         elif elem == TARGET:
#                             yield r' & ' + elem.formatted(formatType, False)
#                         else:
#                             yield r' & ' + elem.formatted(formatType, False)
#             yield '} & ~ \n'
#             yield r'\end{array}'
#             if fence: yield '\n' + r'\right]'
#         else:
#             yield Operation.formatted(self, formatType, fence)
    
# CIRCUIT = Literal(pkg, 'CIRCUIT', operationMaker = lambda operands : Circuit(operands[0]))

"""                
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
    
    def __init__(self, instanceVars, instanceExpr, conditions=None):
        '''
        Create a special Forall expression with ImplicitIdentities as one or
        more of the instanceVars.  Adds appropriate conditions that restrict
        these to be specialized as one or more identities.
        '''
        Forall.__init__(self, instanceVars, instanceExpr, conditions=ForallWithImplicitIdentities._with_implicit_conditions(instanceVars, conditions))
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
        subbed_expr = self.instanceExpr.substituted(subMap)
        def fixImplicitIdentityWidths(expr):
            if not isinstance(expr, Circuit):
                if isinstance(expr, ExpressionList):
                    for subexpr in expr:
                        fixImplicitIdentityWidths(subexpr) # recurse over an ExpressionList
                if isinstance(expr, Operation):
                    fixImplicitIdentityWidths(expr.etcExpr) # recursively search for Circuit subexpression
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
"""

# class QuantumCircuitException():
#     def __init__(self, msg):
#         self.msg = msg
#     def __str__(self):
#         return self.msg
    
""" 
class Gates(Operation):
    '''
    Represents a column of gate operations in parallel on one or more qubits.
    '''
    
    def __init__(self, *gates):
        Operation.__init__(self, GATE, gates)
        self.gates = gates = self.etcExpr
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
         
    def formatted(self, formatType, fence=False, circuit=None, row=None, column=None, multivar_row=False):
        if formatType == LATEX:
            if row is None:
                # present the whole -- as if it were a circuit with one column
                return Circuit([self]).formatted(formatType, fence)
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
            return Operation.formatted(self, formatType, fence)
        
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

    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            outStr = '\n'
            if fence: outStr += r'\left['
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
                        outStr += '{' + column.formatted(formatType, fence) + '} '
                        # Draw a dotted box around MultiVariable columns to distinguish them from a Gates with a solo MultiVariable.
                        #outStr += r'\gategroup{1}{' + str(k+1) + '}{'+ str(self.nrows) + '}{' + str(k+2) + '}{.}{.5em}'
                    else:
                        outStr += '&' + column.formatted(LATEX, circuit=self, row=row, column=k, multivar_row=(row in self.multivar_rows))
            outStr += '}\n' + r'\end{array}' + '\n'
            if fence: outStr += r'\right]'
            return outStr
        else:
            return Operation.formatted(self, formatType, fence)
        
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
            return circuit.reverseCzDn.specialize({Aetc:multiA_val, multiB:multiB_val, Cetc:multiC_val, multiD:multiD_val})
        elif target == Z and control_type == CTRL_UP:
            return circuit.reverseCzUp.specialize({Aetc:multiA_val, multiB:multiB_val, Cetc:multiC_val, multiD:multiD_val})
        elif target == X and control_type == CTRL_DN:
            return circuit.reverseCnotDnToUp.specialize({Aetc:multiA_val, multiB:multiB_val, Cetc:multiC_val, multiD:multiD_val})
        elif target == X and control_type == CTRL_UP:
            return circuit.reverseCnotUpToDn.specialize({Aetc:multiA_val, multiB:multiB_val, Cetc:multiC_val, multiD:multiD_val})
        

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
    
    def __init__(self, instanceVars, instanceExpr, conditions=None):
        '''
        Create a special Forall expression with ImplicitIdentities as one or
        more of the instanceVars.  Adds appropriate conditions that restrict
        these to be specialized as one or more identities.
        '''
        Forall.__init__(self, instanceVars, instanceExpr, conditions=ForallWithImplicitIdentities._with_implicit_conditions(instanceVars, conditions))
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
        subbed_expr = self.instanceExpr.substituted(subMap)
        def fixImplicitIdentityWidths(expr):
            if not isinstance(expr, Circuit):
                if isinstance(expr, ExpressionList):
                    for subexpr in expr:
                        fixImplicitIdentityWidths(subexpr) # recurse over an ExpressionList
                if isinstance(expr, Operation):
                    fixImplicitIdentityWidths(expr.etcExpr) # recursively search for Circuit subexpression
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
            
"""            
