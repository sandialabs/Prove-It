from proveit import Function, Literal

class Stabilizer(Function):
    '''
    Given a stablizer code C (such as a surface code),
    Stabilizer(C) represents the stabilizer of C, i.e., when formally
    conceptualizing the stablizer code C as a subspace of some larger
    Hilbert space, Stabilizer(C) represents the set of Pauli group
    operators P that act trivially on the subspace C: for all c in C,
    we have P c  = c.
    Currently a 'surface code' is poorly defined in surface_code.py,
    implicitly referring to the collection of data qubits, measurement
    qubits, and pattern of connections, rather than the subspace
    being preserved.
    '''

    # the literal operator for the Stabilizer operation
    _operator_ = Literal(
            string_format='stabilizer',
            latex_format=r'\mathrm{stabilizer}\!', theory=__file__)

    def __init__(self, sc, *, styles=None):
        '''
        Create a Stabilizer expression, stabilizer(sc), representing
        the stabilizer for some stabilizer code sc.
        '''
        Function.__init__(
                self, Stabilizer._operator_, sc, styles=styles)