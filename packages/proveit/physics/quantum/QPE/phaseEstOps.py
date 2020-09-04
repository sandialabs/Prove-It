from proveit import Literal, Operation
# from proveit.basiclogic.genericOps import BinaryOperation
# from proveit.number.numberSets import NumberOp, Integers

pkg = __package__ # delete later?

class QPE(Operation):
    '''
    Represents the quantum circuit for the quantum phase estimation
    algorithm. 
    '''
    # the literal operator of the QPE operation
    _operator_ = Literal(stringFormat='QPE', latexFormat = r'{\rm QPE\;}',
                         context=__file__)

    def __init__(self, U, t):
        '''
        Phase estimator circuit for Unitary U and t register qubits.
        '''
        Operation.__init__(self, QPE._operator_, (U, t))


class PhaseEst(Operation):
    '''
    Represents the quantum circuit for estimating the phase.  The
    quantum phase estimation algorithm consists of a PHASE_ESTIMATOR
    followed by quantum fourier transform.
    '''
    # the literal operator of the PhaseEst operation
    _operator_ = Literal(stringFormat='PHASE_EST',
                         latexFormat = r'{\rm PHASE\_EST\;}', context=__file__)

    def __init__(self, U, t):
        '''
        Phase estimator circuit for Unitary U and t register qubits.
        '''
        Operation.__init__(self, PhaseEst._operator_, (U, t))
        

class Psuccess(Operation):
    '''
    Probability of success for a given epsilon where success is
    defined as the measured theta_m being with epsilon of the true
    theta (phase).
    '''
    # the literal operator of the Psuccess operation
    _operator_ = Literal(stringFormat='Psuccess',
                         latexFormat = r'P_{\rm success}', context=__file__)

    def __init__(self, eps):
        '''
        P_success(eps)
        '''
        Operation.__init__(self, Psuccess._operator_, eps)
        

class Pfail(Operation):
    '''
    Probability of failure for a given epsilon where success is
    defined as the measured theta_m being within epsilon of the true
    theta (phase).
    '''
    # the literal operator of the Pfail operation
    _operator_ = Literal(stringFormat='Pfail',
                         latexFormat = r'P_{\rm fail}', context=__file__)

    def __init__(self, eps):
        '''
        P_fail(eps)
        '''
        Operation.__init__(self, Pfail._operator_, eps)
        

# Comment from wdc on Sun 1/26/2020
# This is the original ModAdd() operation class.
# See below for attempts to update to current Prove-It.
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

class ModAdd(Operation):
    '''
    Addition module 2^t
    Generated/updated from original above by wdc, beginning 1/26/2020.
    This depends on the modAdClosure thm in the quantum/QPE context,
    BUT that theorem ipynb also requires items from this phaseEstOps.py
    file, in particular requiring this same ModAdd operation class.
    '''
    # the literal operator of the ModAdd operation class
    _operator_ = Literal('MOD_ADD', latexFormat = r'\oplus',
                         context=__file__)

    def __init__(self, a, b):
        Operation.__init__(self, ModAdd._operator_, (a, b))

    def _closureTheorem(self, numberSet):
        from .theorems import modAddClosure
        if numberSet == Integers:
            return modAddClosure


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
