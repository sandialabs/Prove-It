import sys
from collections import deque
from proveit import (Literal, Function, NamedExprs, safe_dummy_var,
                     ProofFailure, StyleOptions, USE_DEFAULTS, defaults,
                     equality_prover)
from proveit import A, B, C, D, E, F, G, h, i, j, k, m, n, p, Q, R, S, U
from proveit._core_.expression.composite import ExprArray, ExprTuple, ExprRange
from proveit.logic import Equals, Set
from proveit.numbers import one, num, Interval, Add, Neg, subtract


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
    def __init__(self,  operator, operands, *, styles=None):
        Function.__init__(self, operator, operands, styles=styles)

    def latex(self, *, within_qcircuit=False, 
              show_explicitly=True, **kwargs):
        '''
        Format the latex of the QcircuitElement.
        If within_qcircuit is false, we must wrap the LaTeX within
        a \Qcircuit command.
        If a 'wrapper' function is given, use it to
        generate dressed-up latex for the operand.
        '''
        out_str = self.circuit_elem_latex(
                show_explicitly=show_explicitly)
        if not within_qcircuit:
            # Do display it properly on its own, we need to
            # wrap it in a \Qcircuit latex command.
            spacing = '@C=1em @R=.7em'
            out_str = (r'\begin{array}{c} \Qcircuit' + spacing + 
                       '{' + '\n' + '& ' + out_str)
            circuit_elem = self
            if isinstance(self, MultiQubitElem):
                circuit_elem = self.element
            if (not isinstance(circuit_elem, Output) and
                    not isinstance(circuit_elem, Measure)):
                out_str += r' & \qw'
            out_str += ' \n' + r'} \end{array}'
        return out_str
    
    def circuit_elem_latex(self, *, show_explicitly):
        '''
        LaTeX of the circuit element that may be inserted within a
        \Qcircuit LaTeX command given the LaTeX of the operand.
        If 'show_explicitly' is True, show targets of  MultiQubitGates
        explicitly and show 'part' numbers parts of a 
        multi-gate/input/output/measure operation explicitly.
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

    def __init__(self, state, *, part=None, styles=None):
        '''
        Create an INPUT operation (for entering the left-hand side
        of a circuit) with the given input state.
        '''
        if part is None:
            operands = NamedExprs(("state", state))
        else:
            operands = NamedExprs(("state", state), ("part", part))
        QcircuitElement.__init__(self, Input._operator_, operands, 
                                 styles=styles)

    def circuit_elem_latex(self, *, show_explicitly):
        '''
        Display the LaTeX for this Input circuit element.
        '''
        if show_explicitly and hasattr(self, 'part'):
            return r'\qin{%s~\mbox{part}~%s}'%(self.state.latex(), self.part.latex())
        return r'\qin{' + self.state.latex() + r'}'


class Output(QcircuitElement):
    '''
    Represents an output state exiting from the right-hand side of
    a circuit.
    '''
    # the literal operator of the Output operation class
    _operator_ = Literal('OUTPUT', theory=__file__)

    def __init__(self, state, *, part=None, styles=None):
        '''
        Create an OUTPUT operation with the given input state.
        '''
        if part is None:
            operands = NamedExprs(("state", state))
        else:
            operands = NamedExprs(("state", state), ("part", part))
        QcircuitElement.__init__(self, Output._operator_, 
                                 operands, styles=styles)

    def circuit_elem_latex(self, *, show_explicitly):
        '''
        Display the LaTeX for this Output circuit element.
        '''
        if show_explicitly and hasattr(self, 'part'):
            return r'& \qout{%s~\mbox{part}~%s}'%(self.state.latex(), self.part.latex())
        return r'& \qout{' + self.state.latex() + r'}'

class Measure(QcircuitElement):
    '''
    Represents a measurement element of a quantum circuit.
    '''
    # the literal operator of the Output operation class
    _operator_ = Literal('MEASURE', theory=__file__)

    def __init__(self, basis, *, part=None, styles=None):
        '''
        Create an OUTPUT operation with the given input state.
        '''
        if part is None:
            operands = NamedExprs(("basis", basis))
        else:
            operands = NamedExprs(("basis", basis), ("part", part))
        QcircuitElement.__init__(self, Measure._operator_, operands, 
                                 styles=styles)

    def style_options(self):
        '''
        Return the StyleOptions object for this Gate object.
        '''
        from proveit.physics.quantum import Z
        options = StyleOptions(self)
        if self.basis == Z:
            # For an Z measurement, we can use an implicit meter
            # representation.
            options.add_option(
                name='representation',
                description=(
                    "The 'implicit' option formats the Z-measurement "
                    "as a generic meter."),
                default='implicit',
            related_methods=())

        return options

    def circuit_elem_latex(self, *, show_explicitly):
        '''
        Display the LaTeX for this Output circuit element.
        '''
        from proveit.physics.quantum import Z
        if show_explicitly and hasattr(self, 'part'):            
            return r'& \measure{%s~\mbox{part}~%s}'%(
                    self.basis.latex(), self.part.latex())
        if self.basis==Z and self.get_style('Z', 'implicit')=='implicit':
            return r'& \meter'
        return r'& \measure{' + self.basis.latex() + r'}'

class Gate(QcircuitElement):
    '''
    Represents a gate in a quantum circuit.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('GATE', theory=__file__)

    def __init__(self, operation, *, part=None, styles=None):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        if part is None:
            operands = NamedExprs(("operation", operation))
        else:
            operands = NamedExprs(("operation", operation), ("part", part))
        QcircuitElement.__init__(self, Gate._operator_, operands,
                                 styles=styles)
    
    def style_options(self):
        '''
        Return the StyleOptions object for this Gate object.
        '''
        from proveit.physics.quantum import I, X
        options = StyleOptions(self)
        if self.operation == I:
            # For an I gate, it may be displayed as
            # 'I' (explicit) or as a wire (implicit).
            options.add_option(
                name='representation',
                description=(
                    "The 'implicit' option formats the identity operation as "
                    "a quantum wire versus an 'explicit' gate (box) applying I."),
                default='implicit',
            related_methods=())
        if self.operation == X:
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
        if isinstance(self.operation, Input):
            from proveit.physics.quantum import input_gate_to_ket
            return input_gate_to_ket.instantiate(
                {U: self.operation.state})
        elif isinstance(self.operation, Output):
            from proveit.physics.quantum import output_gate_to_ket
            return output_gate_to_ket.instantiate(
                {U: self.operation.state})
        return QcircuitElement.shallow_simplification(
                self, must_evaluate=must_evaluate)

    def circuit_elem_latex(self, *, show_explicitly):
        '''
        Display the LaTeX for this Gate circuit element.
        '''
        from proveit.physics.quantum import I, X #, MEAS
        out_str = '& '
        #if self.gate_operation == MEAS:
        #    out_str += r'\meter'
        if show_explicitly and hasattr(self, 'part'):
            out_str += r'\gate{%s~\mbox{part}~%s}'%(
                    self.operation.latex(), self.part.latex())
        elif (self.operation == I and 
                self.get_style('representation') == 'implicit'):
            out_str += r'\qw'
        elif (self.operation == X and
                self.get_style('representation') == 'implicit'):
            out_str += r'\targ{}'
        else:
            out_str += r'\gate{' + self.operation.latex() + r'}'
        return out_str

class MultiQubitElem(QcircuitElement):
    '''
    A MultiQubitElem is a quantum circuit element that expresses an 
    operation involving multiple qubits.
    
    There are a few different kinds of MultiQubitElem objects.
    1. A CONTROL with one or more targets.
    2. A SWAP with a target -- these must be mutual.
    3. A "part" of a multi-qubit gate, input, output, or measure.
    4. A MultiQubitElem that reduces to a normal gate, input, output, 
    measure, or empty space. (as a replacement for a general circuit
    element).
    
    The operands are the "element" and the "targets".
    The element is CONTROL/SWAP for #1/#2 respectively.
    The target(s) are qubit indices starting from 1 to specify which
    elemental row is targeted (not the entry-wise row, but the 
    element-wise row w.r.t. the distinction between entries and 
    elements of ExprTuples.)
    For #3, the element is a Gate, Input, Output, or Measure with a
    specified "part" to index, starting with 1, which qubit of the
    multi-qubit operation is represented.  The "targets" 
    The element may be an Input, Output, Measure, or Gate 
    QcircuitElement or CONTROL, CLASSICAL_CONTROL, or SWAP. 
    The "target" should represent all qubits of the circuit that are
    involved in the operation.
    For #4, the element should be a Gate, Input, Output, or Measure
    with no specified part, or just SPACE, and the "targets" should be 
    the empty set.
    
    As stated under #2, a SWAP must be mutual.  This means that each
    qubit should indicate the other as the target.  Simpilarly, a
    controlled-Z expressed in a symmetric manner (with a filled-in
    control dot on each end), should also be mutual CONTROL-type
    MultiQubitElem's in which each qubit targets the other.
    A Toffoli gate should be treated as multiple controlled gates with
    the same target.    
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('MULTI_QUBIT_ELEM', theory=__file__)

    def __init__(self, element, targets, *, styles=None):
        '''
        Create a quantum circuit gate for the given "element" acting
        on the given "targets".
        '''
        QcircuitElement.__init__(self, MultiQubitElem._operator_,
                                 NamedExprs(("element", element),
                                            ("targets", targets)), 
                                 styles=styles)

    def circuit_elem_latex(self, *, show_explicitly):
        '''
        If 'show_explicit_targets' is True, show targets of 
        MultiQubitGates explicitly.  If 'show_part_num' is True,
        show 'part' numbers parts of a multi-gate/input/output/measure
        operation explicitly.
        '''
        from proveit.physics.quantum import (CONTROL, CLASSICAL_CONTROL,
                                             SWAP)
        
        out_str = '& '
        if show_explicitly:            
            # This is either being shown on its own, or it lacks
            # explicit targets.
            out_str = self.element.latex(within_qcircuit=True, 
                                         show_explicitly=True)
            if not isinstance(self.element, QcircuitElement):
                out_str = '& \gate{%s}'%out_str
            out_str = (out_str[:-1] + r'~\mbox{on}~' +
                       self.targets.latex() + '}')
        else:
            # This will be shown in the context of a broader Qcircuit
            # and has explicit qubit positions.
            if self.element == CONTROL:
                out_str += r'\control{} \qw'
            elif self.element == CLASSICAL_CONTROL:
                out_str += r'\control{} \cw'
            elif self.element == SWAP:
                out_str += r'\qswap'
            else:
                out_str = self.element.latex(within_qcircuit=True,
                                             show_explicitly=False)
        return out_str

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Handles "MultiQubitElem(a, Set()) = IdentityOp()" and
        "MultiQubitElem(a, Set(n)) = Gate(a)".
        '''
        from proveit.logic import EmptySet
        from proveit.logic.equality import Equals
        if self.targets == EmptySet:
            return self.unary_reduction()
        elif (isinstance(self.targets, Interval) and 
                  self.targets.lower_bound == self.targets.upper_bound
                  and hasattr(self.element, 'part')):
            return self.unary_reduction()            
        return Equals(self, self).conclude_via_reflexivity()

    @equality_prover('unary_reduced', 'unary_reduce')
    def unary_reduction(self, **defaults_config):
        from proveit.logic import EmptySet
        from proveit.physics.quantum import var_ket_psi
        from proveit.physics.quantum.circuits import (
                unary_multi_qubit_elem_reduction,
                unary_multi_gate_reduction,
                unary_multi_input_reduction,
                unary_multi_output_reduction,
                unary_multi_meas_reduction)
        if (isinstance(self.targets, Interval) and 
                  self.targets.lower_bound == self.targets.upper_bound
                  and hasattr(self.element, 'part')):
            if isinstance(self.element, Gate):
                return unary_multi_gate_reduction.instantiate(
                        {A: self.element.operation,
                         k: self.targets.lower_bound})
            if isinstance(self.element, Input):
                return unary_multi_input_reduction.instantiate(
                        {var_ket_psi: self.element.state,
                         k: self.targets.lower_bound})
            if isinstance(self.element, Output):
                return unary_multi_output_reduction.instantiate(
                        {var_ket_psi: self.element.state,
                         k: self.targets.lower_bound})
            if isinstance(self.element, Measure):
                return unary_multi_meas_reduction.instantiate(
                        {B: self.element.basis,
                         k: self.targets.lower_bound})
        if self.targets != EmptySet:
            raise ValueError("'targes' must be the empty set "
                            "order to invoke unary_reduction")
        return unary_multi_qubit_elem_reduction.instantiate(
            {U: self.gate_operation})


def control_elem(*target_qubit_indices):
    from proveit.physics.quantum import CONTROL
    return MultiQubitElem(CONTROL, Set(*target_qubit_indices))

def swap_elem(target_qubit_idx):
    from proveit.physics.quantum import SWAP
    return MultiQubitElem(SWAP, Set(target_qubit_idx))

def multi_elem_entries(element_from_part, start_qubit_idx, end_qubit_idx,
                       *part_start_and_ends, check_part_index_span=True):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent all parts of a multi-qubit operation in a quantum circuit
    involving all qubits from 'start_qubit_idx' to 'end_qubit_idx.
    There will be an entry for each "part" start/end pair of indices.
    In total, these must start from one, be consecutive, and cover the 
    range from the 'start_qubit_idx' to the 'end_qubit_idx.
    The element_from_part function must return an element corresponding
    to a given 'part'.
    '''
    targets = Interval(start_qubit_idx, end_qubit_idx)
    multi_qubit_gate_from_part = (
            lambda part : MultiQubitElem(element_from_part(part), targets))
    part = one
    if len(part_start_and_ends) == 0:
        raise ValueError("Must specify one or more 'part' start and end "
                         "indices, starting from one and covering the range "
                         "from %s to %s"%(start_qubit_idx, end_qubit_idx))
    for part_start, part_end in part_start_and_ends:
        #try:
        #    Equals(part, part_start).prove()
        #except ProofFailure:
        if part != part_start:
            raise ValueError("Part indices must be provably consecutive "
                             "starting from 1: %s ≠ %s"%(part_start, part))
        if part_start == part_end: # just a single element
            yield multi_qubit_gate_from_part(part)
        else:
            param = safe_dummy_var()
            yield ExprRange(param, 
                            multi_qubit_gate_from_part(param),
                            part_start, part_end)
        part = Add(part_end, one).quick_simplified()
    if not check_part_index_span:
        lhs = Add(part_end, num(-1)).quick_simplified()
        rhs = Add(end_qubit_idx, Neg(start_qubit_idx)).quick_simplified()  
        try:
            try:
                lhs = lhs.simplified()
            except:
                pass
            try:
                rhs = rhs.simplified()
            except:
                pass
            Equals(lhs, rhs).prove()
        except ProofFailure:
            raise ValueError("Part indices must span the range of the "
                             "multi qubit operation: %s ≠ %s"
                             %(lhs, rhs))

def multi_gate_entries(gate_operation, start_qubit_idx, end_qubit_idx,
                       *part_start_and_ends, check_part_index_span=True):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent all parts of a multi-gate in a quantum circuit
    involving all qubits from 'start_qubit_idx' to 'end_qubit_idx.
    There will be an entry for each "part" start/end pair of indices.
    In total, these must start from one, be consecutive, and cover the 
    range from the 'start_qubit_idx' to the 'end_qubit_idx.
    '''
    for entry in multi_elem_entries(
            lambda part : Gate(gate_operation, part=part), 
            start_qubit_idx, end_qubit_idx, *part_start_and_ends,
            check_part_index_span=check_part_index_span):
        yield entry

def multi_input_entries(state, start_qubit_idx, end_qubit_idx,
                       *part_start_and_ends, check_part_index_span=True):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent all parts of a multi-gate in a quantum circuit
    involving all qubits from 'start_qubit_idx' to 'end_qubit_idx.
    There will be an entry for each "part" start/end pair of indices.
    In total, these must start from one, be consecutive, and cover the 
    range from the 'start_qubit_idx' to the 'end_qubit_idx.
    '''
    for entry in multi_elem_entries(
            lambda part : Input(state, part=part), 
            start_qubit_idx, end_qubit_idx, *part_start_and_ends,
            check_part_index_span=check_part_index_span):

        yield entry

def multi_output_entries(state, start_qubit_idx, end_qubit_idx,
                         *part_start_and_ends, check_part_index_span=True):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent all parts of a multi-gate in a quantum circuit
    involving all qubits from 'start_qubit_idx' to 'end_qubit_idx.
    There will be an entry for each "part" start/end pair of indices.
    In total, these must start from one, be consecutive, and cover the 
    range from the 'start_qubit_idx' to the 'end_qubit_idx.
    '''
    for entry in multi_elem_entries(
            lambda part : Output(state, part=part), 
            start_qubit_idx, end_qubit_idx, *part_start_and_ends,
            check_part_index_span=check_part_index_span):
        yield entry

def multi_measure_entries(basis, start_qubit_idx, end_qubit_idx,
                          *part_start_and_ends, check_part_index_span=True):
    '''
    Yield consecutive vertical entries for MultiQubitElem to 
    represent all parts of a multi-gate in a quantum circuit
    involving all qubits from 'start_qubit_idx' to 'end_qubit_idx.
    There will be an entry for each "part" start/end pair of indices.
    In total, these must start from one, be consecutive, and cover the 
    range from the 'start_qubit_idx' to the 'end_qubit_idx.
    '''
    for entry in multi_elem_entries(
            lambda part : Measure(basis, part=part), 
            start_qubit_idx, end_qubit_idx, *part_start_and_ends,
            check_part_index_span=check_part_index_span):
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