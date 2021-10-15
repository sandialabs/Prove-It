from proveit import Literal, Operation
from proveit import n
from proveit.logic import SubsetEq
from proveit.numbers import Complex


class InverseFourierTransform(Operation):
    '''
    Represents the quantum circuit for the (inverse) quantum fourier
    transform algorithm.
    '''

    # the literal operator(s) of the InverseFourierTransform operation
    _operator_ = Literal(
        string_format='FT^{dag}',
        latex_format=r'{\mathrm {FT}}^{\dag}',
        theory=__file__)

    def __init__(self, n, *, styles=None):
        '''
        QFT circuit for n qubits.
        '''
        Operation.__init__(self, InverseFourierTransform._operator_, n,
                           styles=styles)
        self.nqubits = n

    def _formatted(self, format_type, **kwargs):
        formatted_operator = self.operator.formatted(format_type, fence=False)
        formated_nqubits = self.nqubits.formatted(format_type, fence=False)
        return formatted_operator + '_{' + formated_nqubits + '}'

    def deduce_in_vec_space(self, vec_space=None, *, field,
                            **defaults_config):
        from . import invFT_in_SU
        if field != Complex:
            raise NotImplementedError(
                    "NumKet.deduce_in_vec_space only implemented for a "
                    "complex field, not %s."%field)
        _SUdomain = invFT_in_SU.instantiate({n:self.nqubits}).domain
        vspace = _SUdomain.including_vec_space(field=Complex)
        if vec_space is not None and vec_space != vspace:
            raise NotImplementedError(
                    "InverseFourierTransofrm.deduce_in_vec_space only "
                    "implemented to deduce membership in %s, not %s"
                    %(vspace, vec_space))
        sub_rel = SubsetEq(_SUdomain, vspace)
        return sub_rel.derive_superset_membership(self)
