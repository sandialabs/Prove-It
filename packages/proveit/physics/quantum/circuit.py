import sys
from proveit import Lambda, Literal, Operation, TransitiveRelation, USE_DEFAULTS, defaults
from proveit._common_ import A, B, C, D, E, F, G, h, i, j, k, m, n, p, Q, R, S, U
from proveit._core_.expression.composite import ExprArray, ExprTuple, ExprRange
from proveit.logic import Set
# from proveit.physics.quantum._common_ import Xgate, Ygate, Zgate, Hgate
# not clear yet what to substitute for ExpressionTensor -- perhaps ExprArray
# and Block is not being used in the active code
# from proveit.multi_expression import ExpressionTensor, Block
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
    Represents an input state entering from the left-hand side of a
    circuit. Updated 1/26/2020 by wdc
    '''
    # the literal operator of the Input operation class
    _operator_ = Literal('INPUT', theory=__file__)
    
    def __init__(self, state):
        '''
        Create an INPUT operation (for entering the left-hand side
        of a circuit) with the given input state.
        '''
        Operation.__init__(self, Input._operator_, state)
        self.state = state

    def formatted(self, format_type, fence=False):
        formatted_state = self.state.formatted(format_type, fence=False)
        if format_type == 'latex':
            spacing = '@C=1em @R=.7em'
            out_str = r'\hspace{2em} \Qcircuit' + spacing + '{' + '\n' + '& '
            out_str += r'\lstick{' + formatted_state + r'}'
            out_str += ' \n' + r'} \hspace{2em}'
            return out_str
        else:
            return 'Input(' + formatted_state + ')'

    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')


# INPUT = Literal(pkg, 'INPUT')  # , operation_maker=lambda operands: Input(*operands))
# An input state (entering the left of the circuit)


class Output(Operation):
    '''
    Represents an output state exiting from the right-hand side of
    a circuit. Updated 1/26/2020 by wdc
    '''
    # the literal operator of the Output operation class
    _operator_ = Literal('OUTPUT', theory=__file__)
    
    def __init__(self, state):
        '''
        Create an OUTPUT operation with the given input state.
        '''    
        Operation.__init__(self, Output._operator_, state)
        self.state = state
    
    def formatted(self, format_type, fence=False):
        formatted_state = self.state.formatted(format_type, fence=False)
        if format_type == 'latex':
            spacing = '@C=1em @R=.7em'
            out_str = r'\hspace{2em} \Qcircuit' + spacing + '{' + '\n' + '& '
            out_str += r'\rstick{' + formatted_state + r'} \qw'
            out_str += ' \n' + r'} \hspace{2em}'
            return out_str
        else:
            return 'Output(' + formatted_state + ')'

    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')


class IdentityOp(Literal):
    '''
    The quantum identity operator 'I'
    '''

    def __init__(self, explicit=False):
        '''
        Create the Literal 'I'.
        If not 'explicit', just use a wire.
        '''
        if explicit:
            styles = {'gate':'explicit'}
        else:
            styles = {'gate':'wire'}
        Literal.__init__(self, 'I', styles=styles)

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions

        options = StyleOptions(self)
        options.add_option('gate',
                          ("The 'wire' option formats the identity operation as a quantum wire and the 'explicit'"
                           "option formats it as a box containing the I literal"))
        return options
    
    def remake_arguments(self):
        if self.get_style('gate', 'wire')=='explicit':
            yield('explicit', True)

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, gate=None, fence=False):
        if gate is None:
            gate = self.get_style('gate', 'wire')
        if format_type == 'latex':
            spacing = '@C=1em @R=.7em'
            out_str = r'\hspace{2em} \Qcircuit' + spacing + '{' + '\n' + '& '
            if gate == 'wire':
                out_str += r'\qw'
            else:
                out_str += r'\gate{I}'
            out_str += ' \n' + r'} \hspace{2em}'
            return out_str
        else:
            if gate == 'wire':
                return '--'
            else:
                return '[I]'

    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')

# OUTPUT = Literal(pkg, 'OUTPUT')  # , operation_maker=lambda operands: Output(*operands))
# An output state (exiting the right of the circuit)


class Gate(Operation):
    '''
    Represents a gate in a quantum circuit.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('GATE', theory=__file__)
    
    def __init__(self, *operand):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        if len(operand) > 1:
            raise ValueError('Expected one operand, got %s instead.' % len(operand))

        Operation.__init__(self, Gate._operator_, operand)

        if len(operand) == 0:
            self.gate_operation = None
        else:
            self.gate_operation = self.operands[0]

    def auto_reduction(self, assumptions=USE_DEFAULTS):
        '''
        Automatically reduce "Gate() = IdentityOp()".
        '''
        if len(self.operands) == 0:
            from proveit.physics.quantum._axioms_ import empty_gate
            with defaults.disabled_auto_reduction_types as disable_reduction_types:
                disable_reduction_types.add(Gate)
                return empty_gate

        if isinstance(self.gate_operation, Input):
            from proveit.physics.quantum._theorems_ import input_gate_to_ket
            # with defaults.disabled_auto_reduction_types as disable_reduction_types:
            #   disable_reduction_types.add(Gate)

            return input_gate_to_ket.instantiate({U: self.gate_operation.state}, assumptions=assumptions)
        elif isinstance(self.gate_operation, Output):
            from proveit.physics.quantum._theorems_ import output_gate_to_ket
            #with defaults.disabled_auto_reduction_types as disable_reduction_types:
             #   disable_reduction_types.add(Gate)

            return output_gate_to_ket.instantiate({U:self.gate_operation.state}, assumptions=assumptions)

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, **kwargs):
        if self.gate_operation is None:
            formatted_gate_operation = '[]'
        else:
            formatted_gate_operation = self.gate_operation.formatted(format_type, fence=False)
        if isinstance(self.gate_operation, IdentityOp):
            formatted_gate_operation = 'I'
        if format_type == 'latex':
            spacing = '@C=1em @R=.7em'
            out_str = r'\hspace{2em} \Qcircuit' + spacing + '{' + '\n' + '& '
            if formatted_gate_operation == 'MES':
                out_str += r'\meter'
            elif formatted_gate_operation == 'SPACE':
                out_str += formatted_gate_operation
            elif isinstance(self.gate_operation, Input):
                out_str += r'\gate{ Input(' + self.gate_operation.state.formatted(format_type='latex') + ')}'
            elif isinstance(self.gate_operation, Output):
                out_str += r'\gate{ Output(' + self.gate_operation.state.formatted(format_type='latex') + ')}'
            else:
                out_str += r'\gate{' + formatted_gate_operation + r'}'
            out_str += ' \n' + r'} \hspace{2em}'
            return out_str
        else:
            return 'Gate(' + formatted_gate_operation + ')'

    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')


class MultiQubitGate(Operation):
    '''
    Represents a connection of multiple gates.  In a circuit(), each row that contains a member of a MultiQubitGate
    must contain a MultiQubitGate() where the arguments are 1- the name of the gate, and 2- the indices of the other
    gates involved in the MultiQubitGate contained in a Set() starting at index 1, NOT 0.
    For example,  |1> \\control |1> \\ |0> |x| |0> would be represented as
    Circuit(ExprTuple(Input, MultiQubitGate(CONTROL, Set(one, two), Output),
            ExprTuple(Input, MultiQubitGate(X, Set(one, two), Output).
    If there are consecutive rows that contain the same type of gate, they will
    be represented as a block.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('MULTI_QUBIT_GATE', theory=__file__)

    def __init__(self, gate, gate_set, styles=None):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        if isinstance(gate_set, Set):
            self.indices = gate_set.operands
        else:
            self.indices = None
        self.gate_set = gate_set

        self.gate = gate

        if styles is None: styles = dict()
        if 'representation' not in styles:
            styles['representation'] = 'explicit'
        Operation.__init__(self, MultiQubitGate._operator_, (gate, gate_set), styles=styles)
    
    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        representation = self.get_style('representation')
        call_strs = []
        if representation == 'implicit':
            call_strs.append("with_styles(representation='implicit')")
        return call_strs

    def auto_reduction(self, assumptions=USE_DEFAULTS):
        '''
        Automatically reduce "MultiQubitGate(a, Set()) = IdentityOp()" and "MultiQubitGate(a, Set(n)) = Gate(a)".
        '''
        from proveit.numbers import is_literal_int

        if isinstance(self.gate_set, Set) and len(self.gate_set.operands) == 1 and \
                is_literal_int(self.gate_set.operands[0]):
            try:
                return self.unary_reduction(assumptions)
            except:
                # Cannot do the reduction if the operand is not known
                # to be in NaturalPos.
                pass

        if isinstance(self.gate_set, Set) and len(self.gate_set.operands) == 0:
            return self.empty_set_reduction(assumptions)
            # need to implement an empty set reduction theorem



    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions

        options = StyleOptions(self)
        options.add_option('representation',
                           ("'implicit' representation displays X gates as a target, while"
                            "'explicit' representation always displays the type of gate in a box. Ex. |X|"))
        return options

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def unary_reduction(self, assumptions=USE_DEFAULTS):
        from proveit.physics.quantum._theorems_ import unary_multi_qubit_gate_reduction

        if not self.gate_set.operands.singular():
            raise ValueError("Expression must have a single operand in "
                             "order to invoke unary_reduction")
        operand = self.gate_set.operands[0]
        with defaults.disabled_auto_reduction_types as disable_reduction_types:
            disable_reduction_types.add(MultiQubitGate)
            return unary_multi_qubit_gate_reduction.instantiate({U: self.gate, A: operand}, assumptions=assumptions)

    def empty_set_reduction(self, assumptions=USE_DEFAULTS):
        from proveit.physics.quantum._theorems_ import empty_multi_qubit_gate_reduction
        if not len(self.gate_set.operands) == 0:
            raise ValueError("Expression must have an empty Set() in "
                             "order to invoke empty_set_reduction")
        #operand = self.gate_set
        with defaults.disabled_auto_reduction_types as disable_reduction_types:
            disable_reduction_types.add(MultiQubitGate)
            return empty_multi_qubit_gate_reduction.instantiate({U: self.gate}, assumptions=assumptions)

    def formatted(self, format_type, representation=None, **kwargs):
        if representation is None:
            representation = self.get_style('representation', 'explicit')

        formatted_gate_operation = (
            self.gate.formatted(format_type, fence=False))
        if isinstance(self.gate, IdentityOp):
            formatted_gate_operation = 'I'
        if isinstance(self.gate, Input):
            formatted_gate_operation = 'Input(' + self.gate.state.formatted(format_type, fence=False) + ')'
        if isinstance(self.gate, Output):
            formatted_gate_operation = 'Output(' + self.gate.state.formatted(format_type, fence=False) + ')'
        if format_type == 'latex':
            if r'\Qcircuit' in formatted_gate_operation:
                idx = formatted_gate_operation.index('\n')
                formatted_gate_operation = formatted_gate_operation[idx + 3:len(formatted_gate_operation) - 16]
                #add = '& '
                # we add three  to include the n and the & and the space after then &
                # we subtract 16 to get rid of the ending bracket, the \hspace, and \n
            spacing = '@C=1em @R=.7em'
            out_str = r'\hspace{2em} \Qcircuit' + spacing + '{' + '\n' + '& '
            if formatted_gate_operation == 'X' and representation == 'implicit':
               # this is formatted as a target.
                out_str += r'\targ'
            elif formatted_gate_operation == 'CONTROL':
                # this is formatted as a solid dot using \control
                out_str += r'\control \qw'
            elif formatted_gate_operation == 'MES':
                # this is formatted as a solid dot using \control
                out_str += r'\meter'
            elif formatted_gate_operation == r'CLASSICAL\_CONTROL':
                # this is formatted as a solid dot, but with classical wires.
                out_str += r'\control \cw'
            elif formatted_gate_operation == 'SWAP':
                out_str += r'\qswap'
            elif formatted_gate_operation == 'SPACE':
                out_str += formatted_gate_operation

            else:
                from proveit.numbers import is_literal_int
                if isinstance(self.gate_set, Set) and all(is_literal_int(entry) for entry in self.gate_set.operands):
                    # everything is a literal
                    if len(self.gate_set.operands) <= 1:
                        out_str += r'\gate{' + formatted_gate_operation + r'{\Big \{} ' + self.gate_set.formatted(
                            format_type) + r'}'
                    else:
                        out_str += formatted_gate_operation
                else:
                    out_str += r'\gate{' + formatted_gate_operation + r'{\Big \{} ' + self.gate_set.formatted(
                        format_type) + r'}'
                    #out_str += formatted_gate_operation + r'{\Big \{}' + self.gate_set.formatted(format_type)
            out_str += ' \n' + r'} \hspace{2em}'
            return out_str
        else:
            return "MultiQubitGate(" + formatted_gate_operation + ", " + self.gate_set.formatted(format_type) + ')'

    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')

 # original below
 # def formatted(self, format_type, fence=false):
 #     formatted_gate_operation = (
 #             self.gate_operation.formatted(format_type, fence=False))
 #     if format_type == 'latex':
 #         return r'\gate{' + formatted_gate_operation + r'}'
 #     else: return Operation._formatted(self, format_type, fence)


class TargetOperator(Literal):
    def __init__(self, string_format, latex_format=None, theory=None):
        Literal.__init__(self, string_format, latex_format, theory)
    
    def latex(self, **kwargs):
        return r'\oplus'

class Target(Operation):
    '''
    Represents the target of a control.
    Updated 1/26/2020 by wdc.
    '''
    # the literal operator of the Target operation class
    _operator_ = TargetOperator('TARGET', latex_format=r'\targ',  theory=__file__)
    
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

    def formatted(self, format_type, fence=False):
        if format_type == 'latex':
            return r'\targ'
        else:
            return Operation._formatted(self, format_type)


class CircuitEquiv(TransitiveRelation):
    '''
    Class to capture the equivalence of 2 circuits A and B.
    CircuitEquiv(A, B) is a claim that the inputs and outputs of A are
    equivalent to the inputs and outputs of B, regardless of what is in between.
    The CircuitEquiv relation uses the congruence
    symbol to distinguish the CircuitEquiv claim from the stronger claim
    that A = B.
    '''
    # operator for the CircuitEquiv relation
    _operator_ = Literal(string_format='equiv', latex_format=r'\cong',
                         theory=__file__)
    # map left-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_left_sides = dict()
    # map right-hand-sides to Subset Judgments
    #   (populated in TransitivityRelation.derive_side_effects)
    known_right_sides = dict()

    def __init__(self, a, b):
        TransitiveRelation.__init__(self, CircuitEquiv._operator_, a, b)
        self.a = a
        self.b = b

    @staticmethod
    def _lambda_expr(lambda_map, expr_being_replaced, assumptions=USE_DEFAULTS):
        from proveit import ExprRange, InnerExpr
        if isinstance(lambda_map, InnerExpr):
            lambda_map = lambda_map.repl_lambda()
        if not isinstance(lambda_map, Lambda):
            # as a default, do a global replacement
            lambda_map = Lambda.global_repl(lambda_map, expr_being_replaced)
        if len(lambda_map.parameters) != 1:
            raise ValueError("When substituting, expecting a single "
                             "'lambda_map' parameter entry which may "
                             "be a single parameter or a range; got "
                             "%s as 'lambda_map'" % lambda_map)
        if isinstance(lambda_map.parameters[0], ExprRange):
            from proveit.numbers import one
            if lambda_map.parameters[0].start_index != one:
                raise ValueError("When substituting a range, expecting "
                                 "the 'lambda_map' parameter range to "
                                 "have a starting index of 1; got "
                                 "%s as 'lambda_map'" % lambda_map)
        return lambda_map

    """
    def substitution(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x equiv y, and given f(x), derive f(x) equiv f(y).
        f(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from proveit import ExprRange
        from ._axioms_ import substitution
        from proveit._common_ import f, x, y

        lambda_map = CircuitEquiv._lambda_expr(lambda_map, self.lhs, assumptions)
        '''
        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use operands_substitution for ExprTuple
            # substitution.
            from proveit.core_expr_types.operations._axioms_ import \
                operands_substitution
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return operands_substitution.instantiate(
                {n: n_sub, f: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)
        '''
        # Regular single-operand substitution:
        return substitution.instantiate({f: lambda_map, x: self.lhs, y: self.rhs},
                                        assumptions=assumptions)
    """

    def sub_left_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x equiv y, and given P(y), derive P(x) assuming P(y).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.rhs.
        '''
        # from proveit import ExprRange
        from ._theorems_ import sub_left_side_into
        # from ._theorems_ import substitute_truth, substitute_in_true, substitute_falsehood, substitute_in_false
        from proveit._common_ import P, x, y
        # from proveit.logic import TRUE, FALSE
        lambda_map = CircuitEquiv._lambda_expr(lambda_map, self.rhs)

        '''
        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use sub_in_left_operands for ExprTuple
            # substitution.
            from proveit.logic.equality._theorems_ import \
                sub_in_left_operands
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return sub_in_left_operands.instantiate(
                {n: n_sub, P: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)
        
        try:
            # try some alternative proofs that may be shorter, if they
            # are usable
            if self.rhs == TRUE:
                # substitute_truth may provide a shorter proof option
                substitute_truth.instantiate({x: self.lhs, P: lambda_map},
                                           assumptions=assumptions)
            elif self.lhs == TRUE:
                # substitute_in_true may provide a shorter proof option
                substitute_in_true.instantiate({x: self.rhs, P: lambda_map},
                                            assumptions=assumptions)
            elif self.rhs == FALSE:
                # substitute_falsehood may provide a shorter proof option
                substitute_falsehood.instantiate({x: self.lhs, P: lambda_map},
                                               assumptions=assumptions)
            elif self.lhs == FALSE:
                # substitute_in_false may provide a shorter proof option
                substitute_in_false.instantiate({x: self.rhs, P: lambda_map},
                                             assumptions=assumptions)
        except:
            pass
        '''
        return sub_left_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map},
            assumptions=assumptions)

    def sub_right_side_into(self, lambda_map, assumptions=USE_DEFAULTS):
        '''
        From x equiv y, and given P(x), derive P(y) assuming P(x).
        P(x) is provided via lambda_map as a Lambda expression or an
        object that returns a Lambda expression when calling lambda_map()
        (see proveit.lambda_map, proveit.lambda_map.SubExprRepl in
        particular), or, if neither of those, an expression to upon
        which to perform a global replacement of self.lhs.
        '''
        from proveit import ExprRange
        from ._theorems_ import sub_right_side_into
        # from ._theorems_ import substitute_truth, substitute_in_true, substitute_falsehood, substitute_in_false
        # from proveit.logic import TRUE, FALSE
        from proveit._common_ import P, x, y
        lambda_map = CircuitEquiv._lambda_expr(lambda_map, self.lhs)

        '''
        if isinstance(lambda_map.parameters[0], ExprRange):
            # We must use sub_in_right_operands for ExprTuple
            # substitution.
            from proveit.logic.equality._theorems_ import \
                sub_in_right_operands
            from proveit.numbers import one
            assert lambda_map.parameters[0].start_index == one
            n_sub = lambda_map.parameters[0].end_index
            return sub_in_right_operands.instantiate(
                {n: n_sub, P: lambda_map, x: self.lhs, y: self.rhs},
                assumptions=assumptions)

        try:
            # try some alternative proofs that may be shorter, if they are usable
            if self.lhs == TRUE:
                # substitute_truth may provide a shorter proof options
                substitute_truth.instantiate({x: self.rhs, P: lambda_map},
                                           assumptions=assumptions)
            elif self.rhs == TRUE:
                # substitute_in_true may provide a shorter proof options
                substitute_in_true.instantiate({x: self.lhs, P: lambda_map},
                                            assumptions=assumptions)
            elif self.lhs == FALSE:
                # substitute_falsehood may provide a shorter proof options
                substitute_falsehood.instantiate({x: self.rhs, P: lambda_map},
                                               assumptions=assumptions)
            elif self.rhs == FALSE:
                # substitute_in_false may provide a shorter proof options
                substitute_in_false.instantiate({x: self.lhs, P: lambda_map},
                                             assumptions=assumptions)
        except:
            pass
        '''
        return sub_right_side_into.instantiate(
            {x: self.lhs, y: self.rhs, P: lambda_map},
            assumptions=assumptions)

    #def string(self, **kwargs):
     #   return self.formatted('string', **kwargs)

    #def latex(self, **kwargs):
     #   return self.formatted('latex', **kwargs)

   # def formatted(self, format_type, fence=False):
#
 #       if format_type == 'latex':
  #          return self.a.formatted(self.a, format_type) + r'\cong' + self.b.formatted(self.b, format_type)
   #     else:
    #        return Operation._formatted(self, format_type)

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
    
#     def formatted(self, format_type, fence=False):
#         formatted_number = self.number.formatted(format_type, fence=False)
#         if format_type == LATEX:
#             return r'/^{' + formatted_number + r'} \qw' 
#         else: return Operation.formatted(self, format_type, fence)

# MULTI_WIRE = Literal(pkg, 'MULTI_WIRE', operation_maker = lambda operands : MultiWire(*operands))


class Circuit(Operation):
    '''
    Represents a quantum circuit as a 2-D ExprArray
    '''
    # literal operator for the Circuit Class
    _operator_ = Literal('CIRCUIT', theory=__file__)
    DEFAULT_SPACING = '@C=1em @R=.7em'

    def __init__(self, array, styles=None):
        '''
        Initialize an ExprTuple from an iterable over Expression
        objects.
        '''
        if styles is None: styles = dict()
        if 'orientation' not in styles:
            styles['orientation'] = 'horizontal'

        if 'spacing' not in styles:
            styles['spacing'] = Circuit.DEFAULT_SPACING

        Operation.__init__(self, Circuit._operator_, [array], styles=styles)

        self.array = array

        if not isinstance(self.array, ExprArray): #or len(self.operands) != 1:
            raise ValueError("Expected contents of a Circuit expression to be an ExprArray object not %s"
                             % str(self.operands.__class__))

        for entry in self.array:
            if not isinstance(entry, ExprTuple) and not isinstance(entry, ExprRange):
                raise ValueError("Contents of an ExprArray must be wrapped in either an ExprRange or ExprTuple.")

        # check each column for same expression throughout
        self.check_range()
        self.check_indices()

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        orientation = self.get_style('orientation')
        spacing = self.get_style('spacing')
        styles = [('orientation', orientation), ('spacing', spacing)]
        defaults = {'orientation':'horizontal', 'spacing':Circuit.DEFAULT_SPACING}
        styles = [(name,value) for name, value in styles if value != defaults[name]]
        call_strs = []
        if len(styles) > 0:
            call_strs.append("with_styles(" + ", ".join("%s = '%s'"%(name, value) for name, value in styles) + ")")
        return call_strs
    
    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions

        options = StyleOptions(self)
        options.add_option('spacing',
                          ("change the spacing of a circuit using the format '@C=1em @R=.7em' where C is the column"
                           " spacing and R is the row spacing"))

    def replace_equiv_circ(self, current, new, assumptions=USE_DEFAULTS):
        '''
        Given the piece that is to be replaced, and the piece it is being replaced with,
        use either space_equiv or time_equiv to prove the replacement.
        '''
        from ._theorems_ import sing_time_equiv, time_equiv, sing_space_equiv, two_qubit_space_equiv
        if not isinstance(current, Circuit):
            raise ValueError('The current circuit piece must be a circuit element.')
        if not isinstance(new, Circuit):
            raise ValueError('The replacement piece must be a circuit element.')
        if current.get_col_height() != new.get_col_height() or current.get_row_length() != new.get_row_length():
            raise ValueError('The current circuit element and the replacement circuit element must be the same size.')
        if current.get_row_length() == 1 and current.get_col_height() == self.get_col_height():
            #return sing_time_equiv.instantiate({h:l, k:l, m: self.get_col_height, n:l, A:l, B: current, C:l, D: new, R:l, S: , Q:l},
             #           assumptions=assumptions)
            pass

    def check_range(self):
        '''
        If there is an ExprRange contained in the circuit,
        every item in the same column MUST agree in length
        of the ExprRange.  If not, raise an error.
        '''
        pos = []

        for m, expr in enumerate(self.array):
            k = 0
            # cycle through the rows
            if isinstance(expr, ExprTuple):
                count = 0
                # counting to make sure every row is the same length
                for i, entry in enumerate(expr):
                    # cycle through each member of the row
                    if isinstance(entry, ExprRange):
                        if m == 0:
                            # if this is the first row
                            #print(entry.first(), entry.last())
                            placeholder = []
                            placeholder.append(i)
                            # adding the column number
                            if isinstance(entry.first(), MultiQubitGate):
                                placeholder.append(entry.first().gate.indices[0])
                            elif isinstance(entry.first(), Gate):
                                placeholder.append(entry.first().gate_operation.indices[0])
                            else:
                                placeholder.append(entry.first().start_index)
                            # add the row index, eg for Aij, we add j for the beginning and the end.
                            # accessing j is different for a MultiQubitGate.
                            if isinstance(entry.last(), MultiQubitGate):
                                placeholder.append(entry.last().gate.indices[0])
                            elif isinstance(entry.last(), Gate):
                                placeholder.append(entry.last().gate_operation.indices[0])
                            else:
                                placeholder.append(entry.last().end_index)
                            pos.append(placeholder)
                        else:
                            if len(pos) == 0:
                                raise ValueError('There is an invalid ExprRange in tuple number %s' % str(i))
                            for item in pos:
                                if item[0] == i:
                                    #print(entry.first(), entry.last())
                                    # if we are in the current column
                                    if isinstance(entry.first(), MultiQubitGate):
                                        current = entry.first().gate.indices[0]
                                    elif isinstance(entry.first(), Gate):
                                        current = entry.first().gate_operation.indices[0]
                                    else:
                                        current = entry.first().start_index
                                    # check the current j value against the first row j value
                                    if current != item[1]:
                                        raise ValueError('Columns containing ExprRanges '
                                                         'must agree for every row. %s from %s is '
                                                         'not equal to %s.' % (current, entry.first(), item[1]))
                                    if isinstance(entry.last(), MultiQubitGate):
                                        current = entry.last().gate.indices[0]
                                    elif isinstance(entry.last(), Gate):
                                        current = entry.last().gate_operation.indices[0]
                                    else:
                                        current = entry.last().end_index
                                    if current != item[2]:
                                        raise ValueError('Columns containing ExprRanges '
                                                         'must agree for every row. %s from is '
                                                         'not equal to %s.' % (current, entry.last(), item[2]))
                                    k += 1
                        count += 3
                    else:
                        count += 1

                if count != self.array.get_row_length():
                    raise ValueError('One or more rows are a different length.  Please double check your entries.')
            elif isinstance(expr, ExprRange):
                if isinstance(expr.first(), ExprTuple):
                    first = None
                    last = None
                    for i, entry in enumerate(expr.first()):
                        # loop through the ExprTuple (first)
                        if isinstance(entry, ExprTuple):
                            raise ValueError('Nested ExprTuples are not supported. Fencing is an '
                                             'extraneous feature for the Circuit class.')
                        elif isinstance(entry, ExprRange):
                            if m == 0:
                                # placeholder/pos is only used if the row is an ExprTuple, however, if the first
                                # row is an ExprRange, it needs to be defined here.
                                #print(entry.first(), entry.last())
                                placeholder = []
                                # add which column we are in
                                placeholder.append(i)
                                # add the first and last values for Aij (j)
                                if isinstance(entry.first(), MultiQubitGate):
                                    placeholder.append(entry.first().gate.indices[1])
                                elif isinstance(entry.first(), Gate):
                                    placeholder.append(entry.first().gate_operation.indices[1])
                                else:
                                    placeholder.append(entry.first().start_index)
                                if isinstance(entry.last(), MultiQubitGate):
                                    placeholder.append(entry.last().gate.indices[1])
                                elif isinstance(entry.last(), Gate):
                                    placeholder.append(entry.last().gate_operation.indices[1])
                                else:
                                    placeholder.append(entry.last().end_index)
                                pos.append(placeholder)
                            if first is None:
                                # first and last are only used by ExprRange
                                if isinstance(entry.first(), MultiQubitGate):
                                    first = entry.first().gate.indices[0]
                                elif isinstance(entry.first(), Gate):
                                    first = entry.first().gate_operation.indices[0]
                                else:
                                    first = entry.first().start_index
                            if isinstance(entry.first(), MultiQubitGate):
                                current = entry.first().gate.indices[0]
                            elif isinstance(entry.first(), Gate):
                                current = entry.first().gate_operation.indices[0]
                            else:
                                current = entry.first().start_index
                            if first != current:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (first, entry.first(), current))
                            k += 1
                        elif isinstance(entry, MultiQubitGate):
                            if first is None:
                                first = entry.gate.indices[0]
                            if first != entry.gate.indices[0]:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (first, entry.gate, entry.gate.indices[0]))
                        elif isinstance(entry, Gate):
                            if first is None:
                                first = entry.gate_operation.indices[0]
                            if first != entry.gate_operation.indices[0]:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (first, entry.gate_operation,
                                                                          entry.gate_operation.indices[0]))
                        else:
                            if first is None:
                                first = entry.start_index
                            if first != entry.start_index:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (first, entry, entry.start_index))
                    for entry in expr.last():
                        # loop through the ExprTuple (last)
                        if isinstance(entry, ExprTuple):
                            raise ValueError('Nested ExprTuples are not supported. Fencing is an '
                                             'extraneous feature for the ExprArray class.')
                        elif isinstance(entry, ExprRange):
                            # these checks confirm that everything in this range of a tuple of a range
                            # are in agreement.
                            if last is None:
                                if isinstance(entry.last(), MultiQubitGate):
                                    last = entry.last().gate.indices[0]
                                elif isinstance(entry.last(), Gate):
                                    last = entry.last().gate_operation.indices[0]
                                else:
                                    last = entry.last().end_index
                            if isinstance(entry.last(), MultiQubitGate):
                                current = entry.last().gate.indices[0]
                            elif isinstance(entry.last(), Gate):
                                current = entry.last().gate_operation.indices[0]
                            else:
                                current = entry.last().end_index
                            if last != current:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (last, entry.last(), current))
                        elif isinstance(entry, MultiQubitGate):
                            if last is None:
                                last = entry.gate.indices[0]
                            if last != entry.gate.indices[0]:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (last, entry.gate, entry.gate.indices[0]))
                        elif isinstance(entry, Gate):
                            if last is None:
                                last = entry.gate_operation.indices[0]
                            if last != entry.gate_operation.indices[0]:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (last, entry.gate_operation, entry.indices[0]))
                        else:
                            if last is None:
                                last = entry.end_index
                            if last != entry.end_index:
                                raise ValueError('Rows containing ExprRanges must agree for every column. %s from %s '
                                                 'is not equal to %s.' % (last, entry, entry.end_index))
            n = m

            if k != len(pos):
                if n != 0:
                    raise ValueError('The ExprRange in the first tuple is not in the same column '
                                     'as the ExprRange in tuple number %s' % str(n))

    def check_indices(self):
        '''
        If there is a MultiQubitGate, checks if all indices match up with additional
         MultiQubitGates with identical indices.
        '''
        k = 1
        # k counts the integer rows, j counts the variable rows
        for entry in self.array:
            # cycle through each ExprTuple; k keeps track of which row we are on.
            if isinstance(entry, ExprTuple):
                for i, value in enumerate(entry):
                    # cycle through each row; i keeps track of which column we are on.
                    if isinstance(value, MultiQubitGate):
                        inset = False
                        # a check to see if the current row index is in the set of MultiQubitGate indices
                        if value.indices is not None:
                            for n, number in enumerate(value.indices, 0):
                                # cycle through each row location of each QubitGate; n keeps track of which gate we are on.
                                if self.array.entries[number.as_int() - 1].entries[i].indices != value.indices:
                                    # each list of indices for each MultiQubitGate must match the current one (starting
                                    # at 0).
                                    raise ValueError('Each linked MultiQubitGate must contain the indices of all other '
                                                     'linked MultiQubitGate')
                                if number.as_int() == k:
                                    inset = True
                        #if not inset:
                         #   print(self)
                          #  raise ValueError('The indices of each MultiQubitGate must also contain the index of itself')
                    elif isinstance(value, ExprRange):
                        pass
                k += 1
           # elif isinstance(entry, ExprRange):
            #    if isinstance(entry.first(), ExprTuple):
             #       for i, value in enumerate(entry.first()):
              #          # cycle through the columns
               #         if isinstance(value, MultiQubitGate):
                #            indices = value.sub_expr(1).sub_expr(1)
                 #           gate = value.sub_expr(1).sub_expr(0)
                  #          if indices.sub_expr(1) != gate.sub_expr(1):
                   #             raise ValueError('The set indexed variable must be indexed the same way as the gate '
                    #                             'indexed variable')
                     #   elif isinstance(value, ExprRange):
                      #      # Range of a Tuple of a Range
                       #     indices = value.sub_expr(1).sub_expr(1)
                        #    gate = value.sub_expr(1).sub_expr(0)
                         #   if indices.sub_expr(1) != gate.sub_expr(1):
                          #      raise ValueError('The set indexed variable must be indexed the same way as the gate '
                           #                      'indexed variable')
                            #if indices.sub_expr(0).sub_expr(1) != gate.sub_expr(0).sub_expr(1):
                             #   raise ValueError('The set indexed variable must be indexed the same way as the gate '
                              #                   'indexed variable')
                   # k += 3


    def _find_wires(self):
        '''
        Takes a Circuit object and determines where wires should be
        placed and returns a nested array with the indices. This method
        also determines if and where there will be a block gate.
        '''
        from proveit.numbers.numerals import num
        wire_placement = []
        # list of the wires

        col_with_mqg = dict()
        # keeps track of which columns have a MQG, columns start at 0, rows (top/bottom) start at 1
        for k, entry in enumerate(self.array, 1):
            # loop through each row; k tells us which row we are on
            if isinstance(entry, ExprTuple):
                col = 0
                for value in entry:
                    # loop through each column
                    if isinstance(value, ExprRange):
                        if isinstance(value.first(), MultiQubitGate):
                            j = 0
                            while j < 3:
                                # we count to 3 because there are three items in each row of an ExprRange
                                if str(col) not in col_with_mqg:
                                    col_with_mqg[str(col)] = {'top': k, 'bottom': k}
                                else:
                                    col_with_mqg[str(col)]['bottom'] = k
                                j += 1
                                col += 1
                    elif isinstance(value, MultiQubitGate):
                        if str(col) not in col_with_mqg:
                            col_with_mqg[str(col)] = {'top': k, 'bottom': k}
                        else:
                            col_with_mqg[str(col)]['bottom'] = k
                        col += 1
                    else:
                        col += 1

            elif isinstance(entry, ExprRange):
                if isinstance(entry.first(), ExprTuple):
                    # ExprRange of a ExprTuple
                    col = 0
                    for value in entry.first():
                        # loop through the columns
                        if isinstance(value, MultiQubitGate):
                            if str(col) not in col_with_mqg:
                                col_with_mqg[str(col)] = {'top': k, 'bottom': k}
                            else:
                                col_with_mqg[str(col)]['bottom'] = k
                            col += 1
                        elif isinstance(value, ExprRange):
                            # ExprRange of a ExprTuple of a ExprRange
                            if isinstance(value.first(), MultiQubitGate):
                                j = 0
                                while j < 3:
                                    # we count to 3 because there are 3 elements in each row of an ExprRange
                                    if str(col) not in col_with_mqg:
                                        col_with_mqg[str(col)] = {'top': k, 'bottom': k}
                                    else:
                                        col_with_mqg[str(col)]['bottom'] = k
                                    j += 1
                                    col += 1
                        else:
                            col += 1

        for k, entry in enumerate(self.array, 1):
            # cycle through each ExprTuple; k keeps track of which row we are on.
            row = dict()
            if isinstance(entry, ExprTuple):
                col = 0
                for value in entry:
                    # cycle through each row; i keeps track of which column we are on.
                    '''
                    # commented because right now we don't include explicit circuits in the wire formatting
                    if str(col) in col_with_mqg:
                        if col_with_mqg[str(col)]['top'] <= k < col_with_mqg[str(col)]['bottom']:
                            # if we are between the first and last MQG in this column
                            connect = True
                        else:
                            # we are not between the first and last MQG in this column
                            connect = False
                    else:
                        connect = False
                    '''
                    if isinstance(value, MultiQubitGate) and value.indices is not None:
                        # we only want MQGs that have a valid Set().
                        index = value.indices.index(num(k))
                        # the index of the current position within the MultiQubitGate.indices.  This should be the same
                        # across all gates in the MultiQubitGate
                        if value.gate.string() != 'CONTROL' and \
                                value.gate.string() != 'CLASSICAL\\_CONTROL':
                            # control gates should not be inside of a MultiQubit block gate
                            if index < len(value.indices) - 1:
                                # if this is not the last gate in the multi_qubit_gate
                                if value.indices[index + 1].as_int() == k + 1 and value.gate == \
                                        self.array.entries[value.indices[index + 1].as_int() - 1].entries[col].gate:
                                    # if this gate is the same as the next and the current gate is not the last one in
                                    # the multi_qubit gate
                                    if index == 0 or value.indices[index - 1].as_int() != k - 1 or value.gate != \
                                            self.array.entries[value.indices[index - 1].as_int() - 1].entries[col].gate:
                                        # This is the first in the multi_qubit block gate!
                                        length = 0
                                        n = index
                                        while n + 1 < len(value.indices) and value.indices[n + 1].as_int() == \
                                                k + length + 1 and value.gate == \
                                                self.array.entries[value.indices[n + 1].as_int() - 1].entries[col].gate:
                                            length += 1
                                            n += 1
                                            # count the number of gates that are the same and then add it to the wire
                                            # direction array
                                        row[col] = ['first', length]
                                    else:
                                        # this is not the first in the multi_qubit block gate
                                        row[col] = 'ghost'
                                elif index != 0 and value.indices[index - 1].as_int() == k - 1 and value.gate == \
                                        self.array.entries[value.indices[index - 1].as_int() - 1].entries[col].gate:
                                    # this is the last in the block gate, but it is not the last gate in the
                                    # MultiQubitGate
                                    row[col] = ['ghost', value.indices[index + 1].as_int() - k]
                                else:
                                    # Define the wire_direction for the multi_qubit_gate by taking the next index and
                                    # subtracting the current one
                                    row[col] = value.indices[index + 1].as_int() - k
                            else:
                                # this is the last gate in the MultiQubitGate, so we skip adding the wires
                                if index != 0:
                                    # as long as this is not the only gate in the MultiQubitGate
                                    if value.indices[index - 1].as_int() == k - 1 and value.gate == \
                                            self.array.entries[k - 2].entries[col].gate:
                                        # if this gate equals the gate right above it then this is part of a
                                        # block gate even though it is the last element
                                        # (we have to subtract 2 because just one takes us to the base 0 index and we
                                        # want the one before the index)
                                        row[col] = 'ghost'
                                        '''
                                        if connect:
                                            # if we are in the middle of the first and last MQGs in this column
                                            row[col] = ['ghost', 1]
                                        else:
                                            # this is the last MQG in this column
                                            '''

                                    else:
                                        # this is not part of a blockgate even though it is the last gate in the MQG
                                        '''
                                        if connect:
                                            # if we are in the middle of the first and last MQGs in this column
                                            row[col] = 1
                                        else:
                                            # this is the last MQG in this column
                                            '''
                                        row[col] = 'skip'
                                    '''
                                elif connect:
                                    # if we are in the middle of the first and last MQGs in this column, even though
                                    # this is the only gate in this specific MultiQubitGate
                                    row[col] = 1
                                    '''
                                else:
                                    # this is the only gate in the MultiQubitGate so we skip adding the wires
                                    row[col] = 'skip'
                        else:
                            # there is a control or a classical control
                            # Define the wire_direction for the MultiQubitGate by taking the next index and
                            # subtracting the current one
                            if index < len(value.indices) - 1:
                                # this is not the last gate so we add a wire index
                                row[col] = value.indices[index + 1].as_int() - k
                                '''
                                elif connect:
                                # if we are in the middle of the first and last MQGs in this column, even though this is
                                # the last gate in this particular MQG
                                row[col] = 1
                                '''
                            else:
                                # this is the last gate in this column so we skip adding a wire
                                row[col] = 'skip'
                        col += 1

                    elif isinstance(value, ExprRange):
                        # ExprTuple of an ExprRange
                        j = 0
                        if isinstance(value.first(), MultiQubitGate):
                            while j < 3:
                                # we count to 3 because there are 3 elements in each row of the ExprRange
                                if str(col) in col_with_mqg:
                                    if col_with_mqg[str(col)]['top'] <= k < col_with_mqg[str(col)]['bottom']:
                                        # if we are between the first and last MQG in this column
                                        connect = True
                                    else:
                                        # we are not between the first and last MQG in this column
                                        connect = False
                                else:
                                    connect = False
                                if connect:
                                    # if we are between the first and last MQG in this column, add a wire extending down
                                    row[col] = ['gate', 1]
                                else:
                                    # we are not between the first and last MQG in this column
                                    row[col] = 'gate'
                                j += 1
                                col += 1
                        elif not isinstance(value.first(), Gate):
                            if isinstance(value.first(), Literal):
                                from proveit.physics.quantum._common_ import SPACE, CONTROL, CLASSICAL_CONTROL
                                if value.first() != SPACE or value.first() != CONTROL or \
                                    value.first() != CLASSICAL_CONTROL:
                                    raise TypeError('Operand contained in Circuit must be a MultiQubitGate, Gate, or a '
                                                    'Literal imported from proveit.physics.quantum._common_  %s is not'
                                                    % value.first())
                            else:
                                raise TypeError('Operand contained in Circuit must be a MultiQubitGate, Gate, or a '
                                                'Literal imported from proveit.physics.quantum._common_  %s is not'
                                                % value.first())
                        else:
                            # this is a gate
                            while j < 3:
                                # we count to 3 because there are 3 elements in each row of the ExprRange
                                if str(col) in col_with_mqg:
                                    if col_with_mqg[str(col)]['top'] <= k < col_with_mqg[str(col)]['bottom']:
                                        # if we are between the first and last MQG in this column
                                        connect = True
                                    else:
                                        # we are not between the first and last MQG in this column
                                        connect = False
                                else:
                                    connect = False
                                if j == 1:
                                    # we only wrap the ellipsis in a gate because the first and last are already wrapped
                                    if connect:
                                        # even though this is a gate, we add a wire because it is in between the first
                                        # and last MQG in this column
                                        row[col] = ['gate', 1]
                                    else:
                                        # we don't add a wire because this is a gate and it is not between the first and
                                        # last MQG in this column
                                        row[col] = 'gate'
                                elif connect:
                                    # even though this is a gate, we add a wire because it is between the first and last
                                    # MQG in this column
                                    row[col] = 1

                                j += 1
                                col += 1
                    else:
                        # is none of the above, but we still need to increment the column
                        col += 1

                wire_placement.append(row)

            elif isinstance(entry, ExprRange):
                if isinstance(entry.first(), ExprTuple):
                    # ExprRange of an ExprTuple
                    n = 0
                    while n < 3:
                        # we count to 3 because there are three rows in an ExprRange of an ExprTuple
                        col = 0

                        for item in entry.first():
                            if str(col) in col_with_mqg:
                                if col_with_mqg[str(col)]['top'] <= k < col_with_mqg[str(col)]['bottom']:
                                    # if we are between the first and last MQG in this column
                                    connect = True
                                else:
                                    # we are not between the first and last MQG in this column
                                    connect = False
                            else:
                                connect = False

                            if isinstance(item, ExprRange):
                                # ExprRange of an ExprTuple of an ExprRange
                                j = 0
                                if isinstance(item.first(), MultiQubitGate):
                                    while j < 3:
                                        # we count to 3 because there are 3 elements in each ExprRange (regardless of
                                        # explicit parameterization)
                                        if n == 2:
                                            if connect:
                                                # if we are between the first and last MQG in this column, add a wire
                                                row[col] = ['gate', 1]
                                            else:
                                                # the last row should not have wires.
                                                row[col] = 'gate'
                                        else:
                                            # add wires going down
                                            row[col] = ['gate', 1]
                                        j += 1
                                        col += 1
                                elif not isinstance(item.first(), Gate):
                                    if isinstance(item.first(), Literal):
                                        from proveit.physics.quantum._common_ import SPACE, CONTROL, CLASSICAL_CONTROL
                                        if item.first() != SPACE or item.first() != CONTROL or \
                                                item.first() != CLASSICAL_CONTROL:
                                            raise TypeError(
                                                'Operand contained in Circuit must be a MultiQubitGate, Gate, or a '
                                                'Literal imported from proveit.physics.quantum._common_  %s is not'
                                                % item.first())
                                    else:
                                        raise TypeError(
                                            'Operand contained in Circuit must be a MultiQubitGate, Gate, or a '
                                            'Literal imported from proveit.physics.quantum._common_  %s is not'
                                            % item.first())
                                else:
                                    # this is a gate
                                    if connect:
                                        # even though this is a gate, we are between the first and last MQG in this
                                        # column so we add a wire.
                                        j = 0
                                        while j < 3:
                                            # we count to 3 because there are 3 entries in each row of a ExprRange
                                            row[col] = ['gate', 1]
                                            col += 1
                                            j += 1
                                    else:
                                        # this is not between the first and last MQG in this column so we do not add a
                                        # wire
                                        j = 0
                                        while j < 3:
                                            # we count to 3 because there are 3 entries in each row of a ExprRange
                                            row[col] = 'gate'
                                            col += 1
                                            j += 1

                            elif isinstance(item, MultiQubitGate):
                                # ExprRange of an ExprTuple
                                if n == 2:
                                    # this is the last row in the ExprRange
                                    if connect:
                                        # this is between the first and last MQG in this row.
                                        row[col] = ['gate', 1]
                                    else:
                                        row[col] = 'gate'
                                else:
                                    row[col] = ['gate', 1]
                                col += 1
                            elif not isinstance(item, Gate):
                                if isinstance(item, Literal):
                                    from proveit.physics.quantum._common_ import SPACE, CONTROL, CLASSICAL_CONTROL
                                    if item != SPACE or item != CONTROL or \
                                            item != CLASSICAL_CONTROL:
                                        raise TypeError(
                                            'Operand contained in Circuit must be a MultiQubitGate, Gate, or a '
                                            'Literal imported from proveit.physics.quantum._common_  %s is not'
                                            % item)
                                else:
                                    raise TypeError('Operand contained in Circuit must be a MultiQubitGate, Gate, or a '
                                                    'Literal imported from proveit.physics.quantum._common_  %s is not'
                                                    % item)
                            else:
                                # this is a gate
                                if connect:
                                    # even though this is a gate, we add a wire because it is in between the first and
                                    # last MQG in this column
                                    row[col] = ['gate', 1]
                                else:
                                    # we are not in between the first and last MQG in this column so we don't add a wire
                                    row[col] = 'gate'
                                col += 1

                        wire_placement.append(row)
                        row = dict()
                        n += 1

            else:
                wire_placement.append(row)

        return wire_placement

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, fence=False, sub_fence=False, operator_or_operators=None, implicit_first_operator=False,
                  wrap_positions=None, orientation=None, spacing=None, **kwargs):
        from proveit._core_.expression.expr import Expression
        default_style = ("explicit" if format_type == 'string' else 'implicit')
        out_str = ''
        if len(self.array) == 0 and fence:
            # for an empty list, show the parenthesis to show something.
            return '()'

        if orientation is None:
            orientation = self.get_style('orientation', 'horizontal')

        if spacing is None:
            spacing = self.get_style('spacing', '@C=1em @R=.7em')

        if format_type == 'latex':
            out_str += r'\hspace{2em} \Qcircuit' + spacing + '{' + '\n'

        wires = self._find_wires()
        formatted_sub_expressions = []
        row = 0
        column = 0
        add = ' '
        # what we add in front of the entry
        for entry in self.array.get_formatted_sub_expressions(format_type, orientation, default_style,
                                                                   operator_or_operators):
            if column == self.array.get_row_length() + 1:
                # we add one to compensate for the added wrapping slash
                row += 1
                column = 0

            if format_type == 'latex':
                if entry[0] == '&':
                    entry = entry[2:]
                    add = '& '
                elif column == 0:
                    add = '& '
                else:
                    add = ' '
                if r'\Qcircuit' in entry:
                    idx = entry.index('\n')
                    entry = entry[idx + 3:len(entry) - 16]
                    add = '& '
                    # we add three  to include the n and the & and the space after then &
                    # we subtract 16 to get rid of the ending bracket, the \hspace, and \n
                entry_str = ''

                if entry == 'SPACE':
                    # we have to include the '& ' because it has already been formatted according to an ExprArray
                    # SPACE is formatted as an empty space in the circuit, denoted by '&' for latex and SPACE for string
                    entry_str += add + ' & '
                elif entry == ' WIRE':
                    entry_str += add + r' \cw'

                elif wires is not None and wires[row] is not None and len(wires[row]) != 0 and column in wires[row]:
                    if column == 0:
                        add = '& '
                    if isinstance(wires[row][column], list):
                        # this is the first in a block multiqubit gate
                        if wires[row][column][0] == 'first':
                            entry_str += add + r'\multigate{' + str(wires[row][column][1]) + r'}{' + entry + r'}'
                        elif wires[row][column][0] == 'ghost':
                            # we assume this to be a ghost since there are only two lists: first and ghost
                            entry_str += add + r'\ghost{' + entry + r'} \qwx[' + str(wires[row][column][1]) + r']'
                        elif wires[row][column][0] == 'gate':
                            if len(wires[row][column]) == 3:
                                if r'\gate' in entry:
                                    entry_str += add + entry + r' \qwx[' + str(wires[row][column][1]) + r'] ' \
                                                                       r'\qwx[' + str(wires[row][column][2]) + r']'
                                else:
                                    entry_str += add + r'\gate{' + entry + r'} \qwx[' + str(wires[row][column][1]) + \
                                               r'] \qwx[' + str(wires[row][column][2]) + r']'
                            else:
                                if r'\gate' in entry:
                                    entry_str += add + entry + r' \qwx[' + str(wires[row][column][1]) + r']'
                                else:
                                    entry_str += add + r'\gate{' + entry + r'} \qwx[' + str(wires[row][column][1]) + r']'
                    elif wires[row][column] == 'ghost':
                        # this is a member of a block multiqubit gate
                        entry_str += add + r'\ghost{' + entry + '}'
                    elif wires[row][column] == 'skip':
                        # if we are skipping, we are not adding wires
                        if entry == 'X':
                            entry_str += add + r'\gate{X}'
                        elif entry == r'\control \qw':
                            # this is formatted as a solid dot using \control
                            entry_str += add + r'\control \qw'
                        elif entry == r'\control \cw':
                            # this is formatted as a solid dot, but with classical wires.
                            entry_str += add + r'\control \cw'
                        elif entry == r'\targ':
                            # this is a target X gate (representation=implicit)
                            entry_str += add + entry
                        elif entry == r'\meter':
                            entry_str += add + entry
                        else:
                            if r'\gate' in entry:
                                entry_str += add + entry
                            else:
                                entry_str += add + r'\gate{' + entry + r'}'
                    # if we are adding wires, we add the length according to self.wires
                    elif wires[row][column] == 'gate':
                        # a gate with no wires
                        if entry == r'\targ':
                            entry_str += add + entry
                        elif entry == r'\meter':
                            entry_str += add + entry
                        elif r'\gate' in entry:
                            entry_str += add + entry
                        else:
                            entry_str += add + r'\gate{' + entry + r'}'
                    elif isinstance(wires[row][column], int):
                        # tacks on a wire regardless of the entry
                        if entry == r'\control \qw':
                            # this is formatted as a solid dot using \control
                            entry_str += add + r'\control \qw \qwx[' + str(wires[row][column]) + r']'
                        elif entry == r'\control \cw':
                            # this is formatted as a solid dot, but with classical wires.
                            entry_str += add + r'\control \cw \cwx[' + str(wires[row][column]) + r']'
                        elif entry == r'\targ':
                            entry_str += add + r'\targ \qwx[' + str(wires[row][column]) + r']'
                        elif r'\gate' in entry or entry == r'\meter':
                            entry_str += add + entry + r' \qwx[' + str(wires[row][column]) + r']'
                        else:
                            entry_str += add + r'\gate{' + entry + r'} \qwx[' + str(wires[row][column]) + r']'
                    elif entry == 'X':
                        if entry != 'implicit':
                            # we want to explicitly see the type of gate as a 'letter' representation
                            entry_str += add + r'\gate{' + entry + r'} \qwx[' + str(wires[row][column]) + r']'
                        else:
                            # this is formatted as a target.
                            entry_str += add + r'\targ \qwx[' + wires[row][column] + r']'
                    elif entry == 'I':
                        entry_str += add + r'\gate{I}'
                    elif entry == r'\control \qw':
                        # this is formatted as a solid dot using \ctrl since there is a wire
                        entry_str += add + r'\ctrl{' + str(wires[row][column]) + r'}'
                    elif entry == r'\control \cw':
                        # this is formatted as a solid dot using \ctrl and \cw since there is a classical wire
                        entry_str += add + r'\control \cw \cwx[' + str(wires[row][column]) + r']'
                    elif entry == r'\meter':
                        entry_str += add + entry
                    elif r'\gate' in entry:
                        entry_str += add + entry + r' \qwx[' + str(wires[row][column]) + r']'
                    else:
                        # gate with wire

                        entry_str += add + r'\gate{' + entry + r'} \qwx[' + str(wires[row][column]) + r']'

                    formatted_sub_expressions.append(entry_str)
                else:
                    formatted_sub_expressions.append(add + entry)
            else:

                formatted_sub_expressions.append(add + entry)
            column += 1

        if orientation == "vertical":
            # up until now, the formatted_sub_expression is still
            # in the order of the horizontal orientation regardless of orientation type
            k = 1
            vert = []
            if self.array.get_style('parameterization', default_style) == 'explicit':
                ex = True
            else:
                ex = False
            m = self.array.get_col_height(ex)
            while k <= self.array.get_row_length(ex):
                i = 1
                j = k
                for var in formatted_sub_expressions:
                    if i == j:
                        vert.append(var)
                        m -= 1
                        if m == 0:
                            vert.append(r' \\' + ' \n ')
                            m = self.array.get_col_height(ex)
                        j += self.array.get_row_length(ex)
                    i += 1
                k += 1
            formatted_sub_expressions = vert

        if operator_or_operators is None:
            operator_or_operators = ','
        elif isinstance(operator_or_operators, Expression) and not isinstance(operator_or_operators, ExprTuple):
            operator_or_operators = operator_or_operators.formatted(format_type, fence=False)
        if isinstance(operator_or_operators, str):
            # single operator
            formatted_operator = operator_or_operators
            if operator_or_operators == ',':
                # e.g.: a, b, c, d
                out_str += (' ').join(formatted_sub_expressions)
            else:
                # e.g.: a + b + c + d
                out_str += (' '+formatted_operator+' ').join(formatted_sub_expressions)
        else:
            # assume all different operators
            formatted_operators = []
            for operator in operator_or_operators:
                if isinstance(operator, ExprRange):
                    # Handle an ExprRange entry; here the "operators"
                    # are really ExprRange "checkpoints" (first, last,
                    # as well as the ExprRange body in the middle if
                    # using an 'explicit' style for 'parameterization').
                    # For the 'ellipses', we will just use a
                    # placeholder.
                    be_explicit = self.array.get_style('parameterization', default_style)
                    formatted_operators += operator._formatted_checkpoints(
                        format_type, fence=False, sub_fence=False, ellipses='',
                        use_explicit_parameterization=be_explicit)
                else:
                    formatted_operators.append(operator.formatted(format_type, fence=False, sub_fence=False))
            if len(formatted_sub_expressions) == len(formatted_operators):
                # operator preceeds each operand
                if implicit_first_operator:
                    out_str = formatted_sub_expressions[0]  # first operator is implicit
                else:
                    out_str = formatted_operators[0] + formatted_sub_expressions[0]  # no space after first operator
                out_str += ' '  # space before next operator
                out_str += ' '.join(
                    formatted_operator + ' ' + formatted_operand for formatted_operator, formatted_operand in
                    zip(formatted_operators[1:], formatted_sub_expressions[1:]))
            elif len(formatted_sub_expressions) == len(formatted_operators) + 1:
                # operator between each operand
                out_str = ' '.join(
                    formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in
                    zip(formatted_sub_expressions, formatted_operators))
                out_str += ' ' + formatted_sub_expressions[-1]
            elif len(formatted_sub_expressions) != len(formatted_operators):
                raise ValueError(
                    "May only perform ExprTuple formatting if the number of operators is equal to the number "
                    "of operands(precedes each operand) or one less (between each operand); "
                    "also, operator ranges must be in correspondence with operand ranges.")

        if format_type == 'latex':
            out_str += ' \n' + r'} \hspace{2em}'
        #print(out_str)
        return out_str

    def _config_latex_tool(self, lt):
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
#         self.deepest_nested_tensor_along_row = dict()
#           # map nested tensor (including self) to a list that indicates the deepest nested tensor per row
#         def determine_deepest_nested_tensors(tensor):            
#             '''
#             Determine and set the deepest nested tensor along each row of tensor,
#             applying this recursively for sub-tensors, and return the depth of this tensor.
#             '''
#             max_depth = 1
#             self.deepest_nested_tensor_along_row[tensor] = deepest_nested_tensor_along_row = []
#             for row in range(tensor.shape[0]):
#                 deepest_nested_tensor = None
#                 max_depth_along_row = 1
#                 for col in range(tensor.shape[1]):
#                     if (row, col) in tensor:
#                         cell = tensor[row, col]
#                         if isinstance(cell, ExpressionTensor):
#                             sub_depth = determine_deepest_nested_tensors(cell)
#                             max_depth_along_row = max(max_depth_along_row, sub_depth + 1)
#                             if deepest_nested_tensor is None or sub_depth > max_depth_along_row:
#                                 deepest_nested_tensor = cell
#                 max_depth = max(max_depth, max_depth_along_row + 1)
#                 deepest_nested_tensor_along_row.append(deepest_nested_tensor)
#             return max_depth
#         determine_deepest_nested_tensors(self.tensor)

#     #def substituted(self, expr_map, operation_map=None, relabel_map=None, reserved_vars=None):
#     #    return Circuit(ExpressionTensor.substituted(self, expr_map, operation_map=operation_map,
#     relabel_map=relabel_map, reserved_vars=reserved_vars))
        
#     def _config_latex_tool(self, lt):
#         Operation._config_latex_tool(self, lt)
#         if not 'qcircuit' in lt.packages:
#             lt.packages.append('qcircuit')
        
#     def generate_nested_row_indices(self):
#         '''
#         Generate nested row indices in order from top of the circuit to the bottom.
#         Each nested row index is a list with elements corresponding to each nesting level.
#         '''
#         for row_indices in self._generate_nested_row_indices(self.tensor):
#             yield row_indices

#     def _generate_nested_row_indices(self, circuit_tensor):
#         '''
#         Generate nested row indices in order from top to bottom for a particular nested sub-tensor.
#         Each nested row index is a list with elements corresponding to each nesting level.
#         '''
#         for cur_level_row, deepest_tensor_along_row in enumerate(self.deepest_nested_tensor_along_row[circuit_tensor]):
#             if deepest_tensor_along_row is None: 
#                 yield [cur_level_row]
#             else:
#                 for sub_nested_row in self._generate_nested_row_indices(deepest_tensor_along_row):
#                     yield [cur_level_row] + sub_nested_row

#     def generate_circuit_elements_along_row(self, nested_row_idx):
#         '''
#         Generate the circuit elements, as (level, circuit, row, column) tuples, along a particular
#         nested row (as generated by generate_nested_row_indices).
#         '''
#         for circuit_elem in Circuit._GenerateCircuitElementsAlongRow(self.tensor, nested_row_idx, 0):
#             yield circuit_elem
    
#     @staticmethod
#     def _GenerateCircuitElementsAlongRow(circuit_tensor, nested_row_idx, level):
#         '''
#         Generate the circuit elements, as (level, circuit, row, column) tuples, along a particular
#         nested row (as generated by generate_nested_row_indices) at a particular nesting level.
#         '''
#         from .common import WIRE_UP, WIRE_DN
#         row = nested_row_idx[level]
#         for column in range(circuit_tensor.shape[1]):
#             if (row, column) in circuit_tensor:
#                 cell = circuit_tensor[row, column]
#                 if isinstance(cell, ExpressionTensor):
#                     # nested Tensor
#                     for circuit_elem in Circuit._GenerateCircuitElementsAlongRow(cell, nested_row_idx, level+1):
#                         yield circuit_elem
#                 if isinstance(cell, Output) or cell == WIRE_UP or cell == WIRE_DN:
#                     yield level, circuit_tensor, row, column
#                     break # nothing after the output or when the wire goes up/down (won't work if starting a new wire -- needs work)
#             yield level, circuit_tensor, row, column

#     def number_of_nested_rows(self, circuit_tensor, row):
#         '''
#         Returns the number of rows, including nested rows, spanned by a given row of a circuit_tensor
#         (which may be a nested tensor).
#         '''
#         deepest_tensor_along_row = self.deepest_nested_tensor_along_row[circuit_tensor][row]
#         if deepest_tensor_along_row is None: return 1
#         return sum(self.number_of_nested_rows(deepest_tensor_along_row, sub_row) for sub_row in range(deepest_tensor_along_row.shape[0]))
    
#     @staticmethod
#     def _NearestTarget(circuit_tensor, row, column, direction):
#         '''
#         Report the vertical distance between (row, column) and
#         the nearest Target in the given direction (direction < 0 for up
#         and direction > 0 for down).  Raise an exception if there is
#         anything in between (row, column) and the Target.
#         '''
#         r = row + direction
#         while not (r, column) in circuit_tensor:
#             r += direction
#             if r < 0 or r >= circuit_tensor.shape[1]:
#                 raise QuantumCircuitException('Control with no target at (%d, %d)'%(row, column))                
#         #if not isinstance(self.operands[r, column], Target):
#         #    raise QuantumCircuitException('There must be no non-identity gate between a control and target')
#         return r - row
                    
#     def formatted(self, format_type, fence=False):
#         return ''.join(self.formatter(format_type, fence))
    
#     def formatter(self, format_type, fence=False):
#         from .common import CTRL_UP, CTRL_DN, CTRL_UPDN, WIRE_UP, WIRE_DN, WIRE_LINK
#         if format_type == LATEX:
#             if fence: yield r'\left[' + '\n'
#             yield r'\begin{array}{cc}' + '\n'
#             yield r'\Qcircuit @C=1em @R=.7em {' # + '\n'
#             for nested_row_idx in self.generate_nested_row_indices():
#                 if sum(nested_row_idx) > 0: yield r' \\ ' # previous row has ended
#                 for level, circuit_tensor, row, column in self.generate_circuit_elements_along_row(nested_row_idx):
#                     if not (row, column) in circuit_tensor:
#                         yield r' & \qw' # identity gate is a quantum wire
#                     else:
#                         elem = circuit_tensor[row, column]
#                         if level < len(nested_row_idx)-1:
#                             # we have a multigate
#                             if sum(nested_row_idx[level:]) == 0:
#                                 # we are at the top of the multigate
#                                 num_multi_gate_rows = self.number_of_nested_rows(circuit_tensor, row)
#                                 yield r' & \multigate{' + str(num_multi_gate_rows-1) + '}{' + elem.formatted(format_type, False) + '}'
#                             else:
#                                 # below the top of the multigate, use ghost
#                                 yield r' & \ghost{' + elem.formatted(format_type, False) + '}'
#                         elif elem == WIRE_LINK:
#                             yield r' & \qw' # junction, but the instruction here just needs to continue the horizontal wire
#                         elif elem == CTRL_UP:
#                             yield r' & \ctrl{' + str(Circuit._NearestTarget(circuit_tensor, row, column, -1)) + '}'
#                         elif elem == CTRL_DN:
#                             yield r' & \ctrl{' + str(Circuit._NearestTarget(circuit_tensor, row, column, 1)) + '}'
#                         elif elem == WIRE_UP:
#                             yield r' & \qwx[' + str(Circuit._NearestTarget(circuit_tensor, row, column, -1)) + '] \qw'
#                         elif elem == WIRE_DN:
#                             yield r' & \qwx[' + str(Circuit._NearestTarget(circuit_tensor, row, column, 1)) + '] \qw'
#                         elif elem == CTRL_UPDN:
#                             yield r' & \ctrl{' + str(Circuit._NearestTarget(circuit_tensor, row, column, -1)) + '}'
#                             yield r' \qwx[' + str(Circuit._NearestTarget(circuit_tensor, row, column, 1)) + ']'
#                         elif elem == TARGET:
#                             yield r' & ' + elem.formatted(format_type, False)
#                         else:
#                             yield r' & ' + elem.formatted(format_type, False)
#             yield '} & ~ \n'
#             yield r'\end{array}'
#             if fence: yield '\n' + r'\right]'
#         else:
#             yield Operation.formatted(self, format_type, fence)
    
# CIRCUIT = Literal(pkg, 'CIRCUIT', operation_maker = lambda operands : Circuit(operands[0]))

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
