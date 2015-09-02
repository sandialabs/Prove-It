from proveit.expression import Literal, Operation, LATEX

pkg = __package__

class QFT(Operation):
    '''
    Represents the quantum circuit for the quantum fourier transform algorithm.
    '''
    def __init__(self, n):
        '''
        QFT circuit for n qubits.
        '''
        Operation.__init__(self, n)
        
QFT  = Literal(pkg, 'QFT', {LATEX:r'{\rm QFT}'}, operationMaker = lambda operands : QFT(*operands))
