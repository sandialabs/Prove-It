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
    
    def formatted(self, format_type, fence=False):
        formatted_operator = self.operator.formatted(format_type, fence=False)
        formated_nqubits = self.nqubits.formatted(format_type, fence=False)
        return formatted_operator + '_{' + formated_nqubits + '}'
        
INV_FT  = Literal(pkg, 'INV_FT', {STRING:'FT^{dag}', LATEX:r'{\rm FT}^{\dag}'}, operation_maker = lambda operands : InverseFourierTransform(*operands))
