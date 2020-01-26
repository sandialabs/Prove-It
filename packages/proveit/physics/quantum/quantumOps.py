from proveit import Operation, Literal

pkg = __package__ # delete this later; will no longer be needed

class Bra(Operation):
    '''
    Class to represent a Dirac bra vector of the form ⟨0| or ⟨1|.
    '''
    # the literal operator of the Bra operation
    _operator_ = Literal(stringFormat='BRA', context=__file__)

    def __init__(self, label):
        Operation.__init__(self, Bra._operator_, label)
        self.label = self.operands[0] # might need to change
    
    def _formatted(self, formatType, fence=False):
        if formatType == 'latex':
            return (r'\langle '
                    + self.label.formatted(formatType, fence=False)
                    + r' \rvert')
        else: # using the unicode \u2329 for the left angle bracket
            return (u'\u2329'
                    + self.label.formatted(formatType, fence=False)
                    + '|')


class Ket(Operation):
    '''
    Class to represent a Dirac ket vector of the form |0⟩ or |1⟩.
    '''
    # the literal operator of the Ket operation
    _operator_ = Literal(stringFormat='KET', context=__file__)

    def __init__(self, label):
        Operation.__init__(self, Ket._operator_, label)
        self.label = self.operands[0]
    
    def _formatted(self, formatType, fence=False, no_lvert=False):
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
    _operator_ = Literal(stringFormat='REGISTER_BRA', context=__file__)

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
            # can't seem to get the \prescript latex to work, so
            # temporarily removing it ot push things through -- perhaps
            # mathtools not loading?
            # return (r'\prescript{}{' + formattedSize + r'}\langle '
            #         + formattedLabel + r' \rvert')
            return (r'\{' + formattedSize + r'\}\langle '
                    + formattedLabel + r' \rvert')
        else:
            return '{' + formattedSize + '}_'+u'\u2329'+formattedLabel+'|'


class RegisterKet(Operation):
    '''
    Class to represent a Dirac ket vector that acknowledges the
    size of the register on which it is defined.
    '''
    # the literal operator of the RegisterBra operation
    _operator_ = Literal(stringFormat='REGISTER_KET', context=__file__)

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

    
# class Meas(Operation):
#     def __init__(self, ket):
#         Operation.__init__(self, MEAS, ket)
#         self.ket = ket
    
# MEAS = Literal(pkg, 'MEAS', {LATEX: r'{\cal M}'}, operationMaker = lambda operands : Meas(*operands))

