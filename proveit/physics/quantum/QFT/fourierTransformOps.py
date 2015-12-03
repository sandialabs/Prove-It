from proveit.expression import Literal, Operation, STRING, LATEX

pkg = __package__

class InverseFourierTransform(Operation):
    '''
    Represents the quantum circuit for the quantum fourier transform algorithm.
    '''
    def __init__(self, n):
        '''
        QFT circuit for n qubits.
        '''
        Operation.__init__(self, INV_FT, n)
        self.nqubits = n
    
    def formatted(self, formatType, fence=False):
        formattedOperator = self.operator.formatted(formatType, fence=False)
        formatedNqubits = self.nqubits.formatted(formatType, fence=False)
        return formattedOperator + '_{' + formatedNqubits + '}'
        
INV_FT  = Literal(pkg, 'INV_FT', {STRING:'FT^{dag}', LATEX:r'{\rm FT}^{\dag}'}, operationMaker = lambda operands : InverseFourierTransform(*operands))
