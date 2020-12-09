from proveit import Operation, Literal, Function
from proveit.linalg import SU, TensorExp
from proveit.numbers import num, Complex, Exp

pkg = __package__ # delete this later; will no longer be needed

class Bra(Operation):
    '''
    Class to represent a Dirac bra vector of the form ⟨0| or ⟨1|.
    '''
    # the literal operator of the Bra operation
    _operator_ = Literal(stringFormat='BRA', theory=__file__)

    def __init__(self, label):
        Operation.__init__(self, Bra._operator_, label)
        self.label = self.operands[0] # might need to change
    
    def _formatted(self, formatType, **kwargs):
        if formatType == 'latex':
            return (r'\langle '
                    + self.label.formatted(formatType, fence=False)
                    + r' \rvert')
        else: # using the unicode \u2329 for the left angle bracket
            return (u'\u2329'
                    + self.label.formatted(formatType, fence=False)
                    + '|')

    # could instead use string() or latex() method instead


class Ket(Operation):
    '''
    Class to represent a Dirac ket vector of the form |0⟩ or |1⟩.
    '''
    # the literal operator of the Ket operation
    _operator_ = Literal(stringFormat='KET', theory=__file__)

    def __init__(self, label):
        Operation.__init__(self, Ket._operator_, label)
        self.label = self.operands[0]
    
    def _formatted(self, formatType, no_lvert=False, **kwargs):
        leftStr = r'\lvert ' if formatType == 'latex' else '|'
        if no_lvert: leftStr = ''
        if formatType == 'latex':
            return (leftStr +
                    self.label.formatted(formatType, fence=False) +
                    r' \rangle')
        else: # using the unicode \u232A for the right angle bracket
            return (leftStr
                    + self.label.formatted(formatType, fence=False)
                    + u'\u232A')


class RegisterBra(Operation):
    '''
    Class to represent a Dirac bra vector that acknowledges the
    size of the register. Intended params are not quite clear ...
    '''
    # the literal operator of the RegisterBra operation
    _operator_ = Literal(stringFormat='REGISTER_BRA', theory=__file__)

    def __init__(self, label, size):
        Operation.__init__(self, RegisterBra._operator_, (label, size))
        self.label = self.operands[0]   # value
        self.size  = self.operands[1]   # size of the register
    
    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        # Expression._config_latex_tool(self, lt)
        if not 'mathtools' in lt.packages:
            lt.packages.append('mathtools')
                
    def _formatted(self, formatType, fence=False):
        formattedLabel = self.label.formatted(formatType, fence=False)
        formattedSize = self.size.formatted(formatType, fence=False)
        if formatType == 'latex':
            # can't seem to get the \prescript latex to work, so using
            # a temporary work-around with an 'empty' subscript; much
            # googling hasn't uncovered explanation for why \prescript
            # isn't working in the ipynbs
            # return (r'\prescript{}{' + formattedSize + r'}\langle '
            #         + formattedLabel + r' \rvert')
            return (r'{_{'+formattedSize+r'}}\langle '
                    + formattedLabel + r' \rvert')
        else:
            return '{' + formattedSize + '}_'+u'\u2329'+formattedLabel+'|'


class RegisterKet(Operation):
    '''
    Class to represent a Dirac ket vector that acknowledges the
    size of the register on which it is defined.
    '''
    # the literal operator of the RegisterKet operation
    _operator_ = Literal(stringFormat='REGISTER_KET', theory=__file__)

    def __init__(self, label, size):
        Operation.__init__(self, RegisterKet._operator_, (label, size))
        self.label = self.operands[0]   # value for the ket
        self.size  = self.operands[1]   # size of the register
    
    def _formatted(self, formatType, fence=False, no_lvert=False):
        formattedLabel = self.label.formatted(formatType, fence=False)
        formattedSize = self.size.formatted(formatType, fence=False)
        leftStr = r'\lvert ' if formatType == 'latex' else '|'
        if no_lvert: leftStr = ''
        if formatType == 'latex':
            return (leftStr + formattedLabel + r' \rangle_{'
                    + formattedSize + '}')
        else:
            return (leftStr + formattedLabel + u'\u232A' + '_{'
                    + formattedSize + '}')

    
class Meas(Function):
    '''
    Class to represent the making of a measurement on a ket |𝜑⟩.
    '''
    # the literal operator of the Meas operation
    _operator_ = Literal(stringFormat='MEAS', latexFormat=r'\mathcal{M}',
                         theory=__file__)

    def __init__(self, ket):
        Function.__init__(self, Meas._operator_, ket)
        self.ket = ket


def QubitRegisterSpace(num_Qbits):
    '''
    Transplanted here beginning 2/13/2020 by wdc, from the old
    physics/quantum/common.py
    '''
    # need some extra curly brackets around the Exp() expression
    # to allow the latex superscript to work on something
    # already superscripted
    return TensorExp({Exp(Complex, num(2))}, num_Qbits)

def RegisterSU(n):
    '''
    Transplanted here beginning 2/13/2020 by wdc, from the old
    physics/quantum/common.py
    '''
    return SU(Exp(num(2), n))
