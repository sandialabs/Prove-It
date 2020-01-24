from proveit import Literal, Operation
# from proveit.basiclogic.genericOps import BinaryOperation
# from proveit.number.numberSets import NumberOp, Integers

pkg = __package__

# class QPE(Operation):
#     '''
#     Represents the quantum circuit for the quantum phase estimation algorithm.
#     '''
#     def __init__(self, U, t):
#         '''
#         Phase estimator circuit for Unitary U and t register qubits.
#         '''
#         Operation.__init__(self, QUANTUM_PHASE_ESTIMATION, (U, t))
        
# QUANTUM_PHASE_ESTIMATION  = Literal(pkg, 'QPE', {LATEX:r'{\rm QPE}'}, operationMaker = lambda operands : QPE(*operands))

# class PhaseEst(Operation):
#     '''
#     Represents the quantum circuit for estimating the phase.  The
#     quantum phase estimation algorithm consists of a PHASE_ESTIMATOR
#     followed by quantum fourier transform.
#     '''
#     def __init__(self, U, t):
#         '''
#         Phase estimator circuit for Unitary U and t register qubits.
#         '''
#         Operation.__init__(self, PHASE_ESTIMATION, (U, t))
        
# PHASE_ESTIMATION  = Literal(pkg, 'PHASE_EST', {LATEX:r'{\rm PHASE_EST}'}, operationMaker = lambda operands : PhaseEst(*operands))

# class Psuccess(Operation):
#     '''
#     Probability of success for a given epsilon where success is defined
#     as the measured theta_m being with epsilon of the true theta (phase).
#     '''
#     def __init__(self, eps):
#         '''
#         P_success(eps)
#         '''
#         Operation.__init__(self, P_SUCCESS, eps)
        
# P_SUCCESS = Literal(pkg, 'Psuccess', {LATEX:r'P_{\rm success}'}, operationMaker = lambda operands : Psuccess(*operands))

# class Pfail(Operation):
#     '''
#     Probability of failure for a given epsilon where success is defined
#     as the measured theta_m being with epsilon of the true theta (phase).
#     '''
#     def __init__(self, eps):
#         '''
#         P_fail(eps)
#         '''
#         Operation.__init__(self, P_FAIL, eps)
        
# P_FAIL = Literal(pkg, 'Pfail', {LATEX:r'P_{\rm fail}'}, operationMaker = lambda operands : Pfail(*operands))

# class ModAdd(BinaryOperation, NumberOp):
#     '''
#     Addition module 2^t
#     '''
#     def __init__(self, a, b):
#         BinaryOperation.__init__(self, MOD_ADD, a, b)

#     def _closureTheorem(self, numberSet):
#         from .theorems import modAddClosure
#         if numberSet == Integers:
#             return modAddClosure
    
# MOD_ADD = Literal(pkg, 'MOD_ADD', {LATEX:r'\oplus'}, operationMaker = lambda operands : ModAdd(*operands))

# class SubIndexed(Operation):
#     '''
#     Subscript indexing of a label
#     '''
#     def __init__(self, label, index):
#         '''
#         \alpha_l
#         '''
#         Operation.__init__(self, SUB_INDEXED, [label, index])
#         self.label = label
#         self.index = index
    
#     def formatted(self, formatType, fence=False):
#         formattedLabel = self.label.formatted(formatType, fence=True)
#         formattedIndex = self.index.formatted(formatType, fence=False)
#         return formattedLabel + '_{' + formattedIndex + '}'

# SUB_INDEXED = Literal(pkg, 'SUB_INDEXED', operationMaker = lambda operands : SubIndexed(*operands))

class SubIndexed(Operation):
    '''
    Provide subscript indexing of a label.
    Updated by wdc starting 1/24/2020.
    '''
    # the literal operator of the Subscript operation
    _operator_ = Literal(stringFormat='SUB_INDEXED',
                         context=__file__)

    def __init__(self, label, index):
        Operation.__init__(self, SubIndexed._operator_, (label, index))
        self.label = self.operands[0]
        self.index = self.operands[1]
    
    def _formatted(self, formatType, fence=False):
        formattedLabel = self.label.formatted(formatType, fence=True)
        formattedIndex = self.index.formatted(formatType, fence=False)
        return formattedLabel + '_{' + formattedIndex + '}'

# SUB_INDEXED = Literal(pkg, 'SUB_INDEXED', operationMaker = lambda operands : SubIndexed(*operands))

