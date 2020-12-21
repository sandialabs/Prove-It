from proveit.expression import Literal, Operation, STRING, LATEX
from proveit.basiclogic.generic_ops import BinaryOperation
from proveit.numbers.number_sets import NumberOp, Integer

pkg = __package__


class QPE(Operation):
    '''
    Represents the quantum circuit for the quantum phase estimation algorithm.
    '''

    def __init__(self, U, t):
        '''
        Phase estimator circuit for Unitary U and t register qubits.
        '''
        Operation.__init__(self, QUANTUM_PHASE_ESTIMATION, (U, t))


QUANTUM_PHASE_ESTIMATION = Literal(
    pkg, 'QPE', {
        LATEX: r'{\rm QPE}'}, operation_maker=lambda operands: QPE(
            *operands))


class PhaseEst(Operation):
    '''
    Represents the quantum circuit for estimating the phase.  The
    quantum phase estimation algorithm consists of a PHASE_ESTIMATOR
    followed by quantum fourier transform.
    '''

    def __init__(self, U, t):
        '''
        Phase estimator circuit for Unitary U and t register qubits.
        '''
        Operation.__init__(self, PHASE_ESTIMATION, (U, t))


PHASE_ESTIMATION = Literal(
    pkg, 'PHASE_EST', {
        LATEX: r'{\rm PHASE_EST}'}, operation_maker=lambda operands: PhaseEst(
            *operands))


class Psuccess(Operation):
    '''
    Probability of success for a given epsilon where success is defined
    as the measured theta_m being with epsilon of the true theta (phase).
    '''

    def __init__(self, eps):
        '''
        P_success(eps)
        '''
        Operation.__init__(self, P_SUCCESS, eps)


P_SUCCESS = Literal(
    pkg, 'Psuccess', {
        LATEX: r'P_{\rm success}'}, operation_maker=lambda operands: Psuccess(
            *operands))


class Pfail(Operation):
    '''
    Probability of failure for a given epsilon where success is defined
    as the measured theta_m being with epsilon of the true theta (phase).
    '''

    def __init__(self, eps):
        '''
        P_fail(eps)
        '''
        Operation.__init__(self, P_FAIL, eps)


P_FAIL = Literal(
    pkg, 'Pfail', {
        LATEX: r'P_{\rm fail}'}, operation_maker=lambda operands: Pfail(
            *operands))


class ModAdd(BinaryOperation, NumberOp):
    '''
    Addition module 2^t
    '''

    def __init__(self, a, b):
        BinaryOperation.__init__(self, MOD_ADD, a, b)

    def _closureTheorem(self, number_set):
        from .theorems import mod_add_closure
        if number_set == Integer:
            return mod_add_closure


MOD_ADD = Literal(
    pkg, 'MOD_ADD', {
        LATEX: r'\oplus'}, operation_maker=lambda operands: ModAdd(
            *operands))


class SubIndexed(Operation):
    '''
    Subscript indexing of a label
    '''

    def __init__(self, label, index):
        '''
        \alpha_l
        '''
        Operation.__init__(self, SUB_INDEXED, [label, index])
        self.label = label
        self.index = index

    def formatted(self, format_type, fence=False):
        formatted_label = self.label.formatted(format_type, fence=True)
        formatted_index = self.index.formatted(format_type, fence=False)
        return formatted_label + '_{' + formatted_index + '}'


SUB_INDEXED = Literal(
    pkg,
    'SUB_INDEXED',
    operation_maker=lambda operands: SubIndexed(
        *operands))
