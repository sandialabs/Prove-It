from proveit import Literal, Operation

class InverseFourierTransform(Operation):
    '''
    Represents the quantum circuit for the (inverse) quantum fourier
    transform algorithm.
    '''

    # the literal operator(s) of the InverseFourierTransform operation
    _operator_ = Literal(stringFormat='FT^{dag}',
                         latexFormat=r'{\mathrm {FT}}^{\dag}', context=__file__)

    def __init__(self, n):
        '''
        QFT circuit for n qubits.
        '''
        Operation.__init__(self, InverseFourierTransform._operator_, n)
        self.nqubits = n
    
    def _formatted(self, formatType, fence=False):
        formattedOperator = self.operator.formatted(formatType, fence=False)
        formatedNqubits = self.nqubits.formatted(formatType, fence=False)
        return formattedOperator + '_{' + formatedNqubits + '}'
        