from proveit import Literal, Operation

class InverseFourierTransform(Operation):
    '''
    Represents the quantum circuit for the (inverse) quantum fourier
    transform algorithm.
    '''

    # the literal operator(s) of the InverseFourierTransform operation
    _operator_ = Literal(string_format='FT^{dag}',
                         latex_format=r'{\mathrm {FT}}^{\dag}', theory=__file__)

    def __init__(self, n):
        '''
        QFT circuit for n qubits.
        '''
        Operation.__init__(self, InverseFourierTransform._operator_, n)
        self.nqubits = n
    
    def _formatted(self, format_type, fence=False):
        formatted_operator = self.operator.formatted(format_type, fence=False)
        formated_nqubits = self.nqubits.formatted(format_type, fence=False)
        return formatted_operator + '_{' + formated_nqubits + '}'
        