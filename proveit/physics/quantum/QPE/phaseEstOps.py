from proveit.expression import Literal, Operation, STRING, LATEX
from proveit.basiclogic.genericOps import BinaryOperation

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
        
QUANTUM_PHASE_ESTIMATION  = Literal(pkg, 'QPE', {LATEX:r'{\rm QPE}'}, operationMaker = lambda operands : QPE(*operands))

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
        
PHASE_ESTIMATION  = Literal(pkg, 'PHASE_EST', {LATEX:r'{\rm PHASE_EST}'}, operationMaker = lambda operands : PhaseEst(*operands))

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
        
P_SUCCESS = Literal(pkg, 'Psuccess', {LATEX:r'P_{\rm success}'}, operationMaker = lambda operands : Psuccess(*operands))

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
        
P_FAIL = Literal(pkg, 'Pfail', {LATEX:r'P_{\rm fail}'}, operationMaker = lambda operands : Pfail(*operands))

class ModAdd(BinaryOperation):
    '''
    Addition module 2^t
    '''
    def __init__(self, a, b):
        BinaryOperation.__init__(self, MOD_ADD, a, b)
    
MOD_ADD = Literal(pkg, 'MOD_ADD', {LATEX:r'\oplus'}, operationMaker = lambda operands : ModAdd(*operands))
    
class Alpha(Operation):
    '''
    Amplitude of the output of the quantum phase estimation circuit
    for a particular state l relative to b, the best outcome.
    '''
    def __init__(self, l):
        '''
        \alpha_l
        '''
        Operation.__init__(self, ALPHA, l)
        self.l = l
    
    def formatted(self, formatType, fence=False):
        if formatType == STRING:
            return 'alpha_{' + self.l.formatted(formatType, fence=False) + '}'
        elif formatType == LATEX:
            return r'\alpha_{' + self.l.formatted(formatType, fence=False) + '}'

ALPHA = Literal(pkg, 'ALPHA', operationMaker = lambda operands : Alpha(*operands))
