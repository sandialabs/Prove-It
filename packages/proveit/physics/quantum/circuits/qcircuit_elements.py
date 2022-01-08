import sys
from collections import deque
from proveit import (Literal, Function, 
                     StyleOptions, USE_DEFAULTS, defaults,
                     equality_prover)
from proveit import A, B, C, D, E, F, G, h, i, j, k, m, n, p, Q, R, S, U
from proveit._core_.expression.composite import ExprArray, ExprTuple, ExprRange
from proveit.logic import Set
# from proveit.physics.quantum import Xgate, Ygate, Zgate, Hgate
# not clear yet what to substitute for ExpressionTensor -- perhaps ExprArray
# and Block is not being used in the active code
# from proveit.multi_expression import ExpressionTensor, Block
# from proveit.logic import Forall, Equals, InSet
# from proveit.computer_science.regular_expressions import KleeneRepetition

pkg = __package__  # can probably delete later


extra_commands = r"""
\newcommand{\qin}[1]{*+<.6em>{#1}}
\newcommand{\qout}[1]{*+<.6em>{#1} \qw}
\newcommand{\multiqin}[2]{*+<1em,.9em>{\hphantom{#2}} \POS [0,0]="i",[0,0].[#1,0]="e",!C *{#2},"e"+CR="a","e"+UR="b","e"+DR="c","a"."b"."c" *\frm{)},"i"}
\newcommand{\ghostqin}[1]{*+<1em,.9em>{\hphantom{#1}}}
\newcommand{\multiqout}[2]{*+<1em,.9em>{\hphantom{#2}} \POS [0,0]="i",[0,0].[#1,0]="e",!C *{#2},"e"+CL="a","e"+UL="b","e"+DL="c","a"."b"."c" *\frm{(},"i" \qw}
\newcommand{\ghostqout}[1]{*+<1em,.9em>{\hphantom{#1}} \qw}
"""

def config_latex_tool(lt):
    if 'qcircuit' not in lt.packages:
        lt.packages.append('qcircuit')
    if extra_commands not in lt.preamble:
        lt.preamble += extra_commands

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

class QcircuitElement(Function):
    def __init__(self,  operator, operand_or_operands, *, styles=None):
        Function.__init__(self, operator, operand_or_operands, styles=styles)

    def latex(self, *, within_qcircuit=False, **kwargs):
        '''
        Format the latex of the QcircuitElement.
        If within_qcircuit is false, we must wrap the LaTeX within
        a \Qcircuit command.
        If a 'wrapper' function is given, use it to
        generate dressed-up latex for the operand.
        '''
        out_str = self.circuit_elem_latex(solo=not within_qcircuit)
        if not within_qcircuit:
            # Do display it properly on its own, we need to
            # wrap it in a \Qcircuit latex command.
            spacing = '@C=1em @R=.7em'
            out_str = (r'\begin{array}{c} \Qcircuit' + spacing + 
                       '{' + '\n' + '& ' + out_str + r' & \qw')
            out_str += ' \n' + r'} \end{array}'
        return out_str
    
    def circuit_elem_latex(self, *, solo):
        '''
        LaTeX of the circuit element that may be inserted within a
        \Qcircuit LaTeX command given the LaTeX of the operand.
        If 'solo' is True, it is represented on its own and not within
        a broader circuit.
        '''
        raise NotImplementedError("Must implement for each QcircuitElement")
    
    def _config_latex_tool(self, lt):
        config_latex_tool(lt)


class Input(QcircuitElement):
    '''
    Represents an input state entering from the left-hand side of a
    circuit.
    '''
    # the literal operator of the Input operation class
    _operator_ = Literal('INPUT', theory=__file__)

    def __init__(self, state, *, styles=None):
        '''
        Create an INPUT operation (for entering the left-hand side
        of a circuit) with the given input state.
        '''
        QcircuitElement.__init__(self, Input._operator_, state, styles=styles)
        self.state = state

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Input circuit element.
        '''
        return r'\qin{' + self.state.latex() + r'}'


class Output(QcircuitElement):
    '''
    Represents an output state exiting from the right-hand side of
    a circuit.
    '''
    # the literal operator of the Output operation class
    _operator_ = Literal('OUTPUT', theory=__file__)

    def __init__(self, state, *, styles=None):
        '''
        Create an OUTPUT operation with the given input state.
        '''
        QcircuitElement.__init__(self, Output._operator_, state, styles=styles)
        self.state = state

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Output circuit element.
        '''
        return r'& \qout{' + self.state.latex() + r'}'

class Measure(QcircuitElement):
    '''
    Represents a measurement element of a quantum circuit.
    '''
    # the literal operator of the Output operation class
    _operator_ = Literal('MEASURE', theory=__file__)

    def __init__(self, basis, *, styles=None):
        '''
        Create an OUTPUT operation with the given input state.
        '''
        QcircuitElement.__init__(self, Measure._operator_, basis, styles=styles)
        self.basis = basis

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Output circuit element.
        '''
        return r'& \measureD{' + self.basis.latex() + r'}'

class Gate(QcircuitElement):
    '''
    Represents a gate in a quantum circuit.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('GATE', theory=__file__)

    def __init__(self, operand, *, styles=None):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        QcircuitElement.__init__(self, Gate._operator_, operand, styles=styles)
        self.gate_operation = self.operand
    
    def style_options(self):
        '''
        Return the StyleOptions object for this Gate object.
        '''
        from proveit.physics.quantum import I, X
        options = StyleOptions(self)
        if self.operand == I:
            # For an I gate, it may be displayed as
            # 'I' (explicit) or as a wire (implicit).
            options.add_option(
                name='representation',
                description=(
                    "The 'implicit' option formats the identity operation as "
                    "a quantum wire versus an 'explicit' gate (box) applying I."),
                default='implicit',
            related_methods=())
        if self.operand == X:
            # For an X gate, it may be displayed as
            # 'X' (explicit) or as a target (implicit).
            options.add_option(
                name='representation',
                description=(
                    "The 'implicit' option formats the X gate as "
                    "a target rather than 'X'."),
                default='explicit',
            related_methods=())

        return options
    
    def with_implicit_representation(self):
        return self.with_styles(representation='implicit')

    def with_explicit_representation(self):
        return self.with_styles(representation='explicit')
    
    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        representation = self.get_style('representation', 'default')
        call_strs = []
        if representation == 'implicit':
            call_strs.append("with_implicit_representation()")
        elif representation == 'explicit':
            call_strs.append("with_explicit_representation()")
        return call_strs

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Handles "Gate(Input(U)) = Input(U)",
        and  "Gate(Output(U)) = Output(U)".
        '''
        if isinstance(self.gate_operation, Input):
            from proveit.physics.quantum import input_gate_to_ket
            return input_gate_to_ket.instantiate(
                {U: self.gate_operation.state})
        elif isinstance(self.gate_operation, Output):
            from proveit.physics.quantum import output_gate_to_ket
            return output_gate_to_ket.instantiate(
                {U: self.gate_operation.state})
        return QcircuitElement.shallow_simplification(
                self, must_evaluate=must_evaluate)

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Gate circuit element.
        '''
        from proveit.physics.quantum import I, X #, MEAS
        out_str = '& '
        #if self.gate_operation == MEAS:
        #    out_str += r'\meter'
        if (self.operand == I and 
                self.get_style('representation') == 'implicit'):
            out_str += r'\qw'
        elif (self.operand == X and
                self.get_style('representation') == 'implicit'):
            out_str += r'\targ{}'
        elif isinstance(self.gate_operation, Input):
            out_str += r'\gate{INPUT(' + self.gate_operation.state.latex() + r')}'
        elif isinstance(self.gate_operation, Output):
            out_str += r'\gate{OUTPUT(' + self.gate_operation.state.latex() + r')}'
        else:
            out_str += r'\gate{' + self.gate_operation.latex() + r'}'
        return out_str

class MultiQubitElem(QcircuitElement):
    '''
    A MultiQubitElem is a quantum circuit element that expresses an 
    operation involving multiple qubits.
    
    The sub-expressions are the element and the qubit_positions.
    The element may be an Input, Output, Measure, or Gate 
    QcircuitElement or CONTROL, CLASSICAL_CONTROL, or SWAP. 
    The qubit_positions may be an ExprTuple, Set, or an expression
    representing either of these.
    
    A generic MultiQubitElem will use an expression to represent
    a ExprTuple or Set of qubit_positions that is not an ExprTuple
    or Set.  
    
    For controlled gate, there should be a MultiQubitElem at the
    control with a CONTROL gate_operation, and the qubit_positions
    should be a Set with the positions of the control and the targets.
    It should use a Set since order doesn't matter.  The targets can be
    normal Gate elements but may be multi-gates.
    
    A multi-gate (a tall box covering multiple rows) should use an
    ExprRange of 
    MultiQubitElem objects at the top row of the multi-gate and Ghost elements
    for the other rows.  The qubit_positions should be an ExprTuple
    of the consecutive positions starting with the top 
    "representative".  The order doesn't matter; we must not allow
    the qubits involved in a mult-gate to be permuted.  A controlled 
    gate may have multi-gate target(s); the top "representative" should
    be used as the target.
    
    A Toffoli gate should be treated as multiple controlled gates with
    the same target.
    
    A swap gate should be redudant with two MultiQubitElems using
    SWAP as the gate operation of each.  Each one should list its own 
    position as the first of the qubit_positions and the other as the 
    second.  Although this is redundant, it ensures that there is one 
    way to represent this symmetric operation.
    
    A controlled-Z expressed in a symmetric manner (with a filled-in
    control dot on each end), should be implemented in the redundant
    manner of the swap gate, but with CONTROL as the gate_operation.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('MULTI_QUBIT_ELEM', theory=__file__)

    def __init__(self, element, qubit_positions, *, styles=None):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        from proveit.physics.quantum import (CONTROL, CLASSICAL_CONTROL, 
                                             SWAP)
        Function.__init__(self, MultiQubitElem._operator_,
                           (element, qubit_positions), styles=styles)
        self.element = self.operands[0]
        self.qubit_positions = self.operands[1]
        if element in (CONTROL, CLASSICAL_CONTROL, SWAP):
            return # these are valid
        if (not isinstance(element, Input) and 
                not isinstance(element, Output) and
                not isinstance(element, Measure) and
                not isinstance(element, Gate)):
            raise TypeError("A MultiQubitElem must be either of "
                            "CONTROL, CLASSICAL_CONTROL, SWAP, "
                            "or an Input, Ouput, Measure, or Gate "
                            "QcircuitElement.")

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions

        options = StyleOptions(self)
        # It would be better to make this only an option when it is
        # applicable.  Just doing this for now.
        options.add_option(
            name='representation',
            description=("'implicit' representation displays X gates "
                         "as a target, while 'explicit' representation "
                         "always displays the type of gate in a box. "
                         "Ex. |X|. 'Block' displays the MultiQubitElem "
                         "as a block gate assuming all other gates within"
                         " the MultiQubitElem are the same."),
            default='implicit',
            related_methods=())

        # options.add_option(
        #     name='set_representation',
        #     description=("'implicit' representation does not display the set "
        #                  "but 'explicit representation does. "),
        #     default='default',
        #     related_methods=('with_explicit_set_representation',
        #                      'with_implicit_set_representation'))

        return options

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        representation = self.get_style('representation')
        call_strs = []
        if representation != 'explicit':
            call_strs.append("with_styles(representation='%s')"
                             %representation)
        return call_strs

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this MultiQubitElem circuit element.
        If solo=True, the MultiQubitElem will be display on its own
        rather than in the context of a broader Qcircuit.
        '''
        from proveit.physics.quantum import (CONTROL, CLASSICAL_CONTROL, 
                                             X, SWAP)
        
        out_str = '& '
        if not solo and (isinstance(self.qubit_positions, Set) or
                         isinstance(self.qubit_positions, ExprTuple)):
            # This will be shown in the context of a broader Qcircuit
            # and has explicit qubit positions.
            if self.element == CONTROL:
                out_str += r'\control{} \qw'
            elif self.element == CLASSICAL_CONTROL:
                out_str += r'\control{} \cw'
            if self.element == Gate(X):
                if self.get_style('representation') == 'implicit':
                    out_str += r'\targ'
            elif self.element == SWAP:
                out_str += r'\qswap'
            else:
                out_str = self.element.latex(within_qcircuit=True)
        else:
            # This is either being shown on its own, or it lacks
            # explicit qubit positions.
            out_str = self.element.latex(within_qcircuit=True)
            assert out_str[-1] == '}'
            out_str = (out_str[:-1] + r'~\mbox{on}~' +
                       self.qubit_positions.latex() + '}')
        return out_str

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Handles "MultiQubitElem(a, Set()) = IdentityOp()" and
        "MultiQubitElem(a, Set(n)) = Gate(a)".
        '''
        from proveit.numbers import is_literal_int
        from proveit.logic.equality import Equals
        if (isinstance(self.qubit_positions, ExprTuple) 
                and self.qubit_positions.is_single()
                and is_literal_int(self.gate_set.operands[0])):
            try:
                return self.unary_reduction()
            except BaseException:
                # Cannot do the reduction if the operand is not known
                # to be in NaturalPos.
                pass

        if (isinstance(self.qubit_positions, ExprTuple) and 
                self.qubit_positions.num_entries() == 0):
            return self.empty_set_reduction()
            # need to implement an empty set reduction theorem
        return Equals(self, self).conclude_via_reflexivity()

    @equality_prover('unary_reduced', 'unary_reduce')
    def unary_reduction(self, **defaults_config):
        from proveit.physics.quantum.circuits import (
                unary_multi_qubit_gate_reduction)
        if not isinstance(self.qubit_positions, ExprTuple):
            raise TypeError("'qubit_positions' must be an ExprTuple in "
                            "order to invoke unary_reduction")
        if not self.qubit_positions.is_single():
            raise ValueError("'qubit_positions' must be a singular "
                             "ExprTuple in order to invoke unary_reduction")
        operand = self.qubit_positions.operands[0]
        return unary_multi_qubit_gate_reduction.instantiate(
            {U: self.gate_operation, A: operand})

    @equality_prover('empty_set_reduced', 'empty_set_reduce')
    def empty_reduction(self, **defaults_config):
        from proveit.physics.quantum.circuits import (
                empty_multi_qubit_gate_reduction)
        if not isinstance(self.qubit_positions, ExprTuple):
            raise TypeError("'qubit_positions' must be an ExprTuple in "
                            "order to invoke empty_reduction")
        if self.qubit_positions.num_entries() != 0:
            raise ValueError("'qubit_positions' must be an empty "
                             "ExprTuple in order to invoke empty_reduction")
        return empty_multi_qubit_gate_reduction.instantiate(
            {U: self.gate_operation})

def multi_elem_entries(element, qubit_start_end_indices):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent all parts of a multi-qubit element in a quantum circuit.
    There will be an entry for each start/end pair of indices.
    '''
    from proveit import safe_dummy_var
    for start_and_end in qubit_start_end_indices:
        if len(start_and_end) != 2:
            raise ValueError("'qubit_start_end_indices' should be "
                             "start/end pairs")
    start_index = qubit_start_end_indices[0][0]
    end_index = qubit_start_end_indices[-1][-1]
    qubit_positions = ExprTuple(ExprRange(i, i, start_index, end_index))
    multi_qubit_gate = MultiQubitElem(element, qubit_positions)
    for entry_start_index, entry_end_index in qubit_start_end_indices:
        if entry_start_index == entry_end_index:
            yield multi_qubit_gate
        else:
            yield ExprRange(safe_dummy_var(), multi_qubit_gate,
                            entry_start_index, entry_end_index)


def multi_gate_entries(gate_operation, qubit_start_end_indices):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent all parts of a multi-gate in a quantum circuit.
    There will be an entry for each start/end pair of indices.
    '''
    for entry in multi_elem_entries(Gate(gate_operation), 
                                    qubit_start_end_indices):
        yield entry

def multi_input_entries(state, qubit_start_end_indices):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent a multi-qubit input state in a quantum circuit.
    There will be an entry for each start/end pair of indices.
    '''
    for entry in multi_elem_entries(Input(state), 
                                    qubit_start_end_indices):
        yield entry

def multi_output_entries(state, qubit_start_end_indices):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent a multi-qubit input state in a quantum circuit.
    There will be an entry for each start/end pair of indices.
    '''
    for entry in multi_elem_entries(Output(state), 
                                    qubit_start_end_indices):
        yield entry

def multi_measure_entries(basis, qubit_start_end_indices):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent a multi-qubit measurement in a quantum circuit.
    There will be an entry for each start/end pair of indices.
    '''
    for entry in multi_elem_entries(Measure(basis), 
                                    qubit_start_end_indices):
        yield entry

def multi_wire(size):
    '''
    Create an ExprRange of identity gates that may be represented
    as a multi-wire in a Qcircuit.
    '''
    from proveit import safe_dummy_var
    from proveit.physics.quantum import I
    from proveit.numbers import one
    return ExprRange(safe_dummy_var(), Gate(I), one, size)

"""
class MultiWire(QcircuitElement):
    '''
    Marks a "wire" as a bundle with a number of individual wires.
    '''
    _operator_ = Literal('MULTI_WIRE', theory=__file__)

    def __init__(self, number, *, styles=None):
        '''
        Create a multi-wire.
        '''
        Function.__init__(self, MultiWire._operator_, number,
                          styles=styles)
        self.number = number

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        representation = self.get_style('representation', 'explicit')
        call_strs = []
        if representation != 'explicit':
            call_strs.append("with_styles(representation='%s')"
                             %representation)
        return call_strs

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions

        options = StyleOptions(self)
        # It would be better to make this only an option when it is
        # applicable.  Just doing this for now.
        options.add_option(
            name='representation',
            description=("'implicit' representation displays MutiWire"
                         "objects as an IdentityOp. 'explicit' representation "
                         "displays MultiWire objects as a bundle using the "
                         "backslash notation. "),
            default='explicit',
            related_methods=('with_implicit_style'))

        return options

    def with_implicit_style(self):
        '''
        return a MultiWire object with the implicit style
        '''
        return self.with_styles(representation='implicit')

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this MultiWire circuit element.
        '''
        representation = self.get_style('representation', 'explicit')
        if representation == 'explicit':
            return r'{ /^{' + self.number.latex() + r'} } \qw'
        else:
            return r'\qw'
"""