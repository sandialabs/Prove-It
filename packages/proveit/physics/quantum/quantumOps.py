from proveit.expression import Operation, Literal, LATEX

pkg = __package__

class Bra(Operation):
    def __init__(self, label):
        Operation.__init__(self, BRA, label)
        self.label = label
    
    def formatted(self, formatType, fence=False):
        if formatType == LATEX:
            return r'\langle ' + self.label.formatted(formatType, fence=False) + r' \rvert'
        else:
            return '<'+self.label.formatted(formatType, fence=False)+'|'

BRA = Literal(pkg, 'BRA', operationMaker = lambda operands : Bra(*operands))

class Ket(Operation):
    def __init__(self, label):
        Operation.__init__(self, KET, label)
        self.label = label
    
    def formatted(self, formatType, fence=False, no_lvert=False):
        leftStr = r'\lvert ' if formatType == LATEX else '|'
        if no_lvert: leftStr = ''
        if formatType == LATEX:
            return leftStr + self.label.formatted(formatType, fence=False) + r' \rangle'
        else:
            return leftStr+self.label.formatted(formatType, fence=False)+'>'

KET = Literal(pkg, 'KET', operationMaker = lambda operands : Ket(*operands))

class RegisterBra(Operation):
    def __init__(self, label, size):
        Operation.__init__(self, REGISTER_BRA, [label, size])
        self.label = label
        self.size = size # size of the register
    
    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if not 'mathtools' in lt.packages:
            lt.packages.append('mathtools')
                
    def formatted(self, formatType, fence=False):
        formattedLabel = self.label.formatted(formatType, fence=False)
        formattedSize = self.size.formatted(formatType, fence=False)
        if formatType == LATEX:
            return r'\prescript{}{' + formattedSize + r'}\langle ' + formattedLabel + r' \rvert'
        else:
            return '{' + formattedSize + '}_<'+formattedLabel+'|'

REGISTER_BRA = Literal(pkg, 'REGISTER_BRA', operationMaker = lambda operands : RegisterBra(*operands))

class RegisterKet(Operation):
    def __init__(self, label, size):
        Operation.__init__(self, REGISTER_KET, [label, size])
        self.label = label
        self.size = size # size of the register
    
    def formatted(self, formatType, fence=False, no_lvert=False):
        formattedLabel = self.label.formatted(formatType, fence=False)
        formattedSize = self.size.formatted(formatType, fence=False)
        leftStr = r'\lvert ' if formatType == LATEX else '|'
        if no_lvert: leftStr = ''
        if formatType == LATEX:
            return leftStr + formattedLabel + r' \rangle_{' + formattedSize + '}'
        else:
            return leftStr + formattedLabel + '>_{' + formattedSize + '}'

REGISTER_KET = Literal(pkg, 'REGISTER_KET', operationMaker = lambda operands : RegisterKet(*operands))
    
class Meas(Operation):
    def __init__(self, ket):
        Operation.__init__(self, MEAS, ket)
        self.ket = ket
    
MEAS = Literal(pkg, 'MEAS', {LATEX: r'{\cal M}'}, operationMaker = lambda operands : Meas(*operands))

