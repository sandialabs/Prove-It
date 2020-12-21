from proveit import Operation, Literal, LATEX

pkg = __package__

class Bra(Operation):
    def __init__(self, label):
        Operation.__init__(self, BRA, label)
        self.label = label
    
    def formatted(self, format_type, fence=False):
        if format_type == LATEX:
            return r'\langle ' + self.label.formatted(format_type, fence=False) + r' \rvert'
        else:
            return '<'+self.label.formatted(format_type, fence=False)+'|'

BRA = Literal(pkg, 'BRA', operation_maker = lambda operands : Bra(*operands))

class Ket(Operation):
    def __init__(self, label):
        Operation.__init__(self, KET, label)
        self.label = label
    
    def formatted(self, format_type, fence=False, no_lvert=False):
        left_str = r'\lvert ' if format_type == LATEX else '|'
        if no_lvert: left_str = ''
        if format_type == LATEX:
            return left_str + self.label.formatted(format_type, fence=False) + r' \rangle'
        else:
            return left_str+self.label.formatted(format_type, fence=False)+'>'

KET = Literal(pkg, 'KET', operation_maker = lambda operands : Ket(*operands))

class RegisterBra(Operation):
    def __init__(self, label, size):
        Operation.__init__(self, REGISTER_BRA, [label, size])
        self.label = label
        self.size = size # size of the register
    
    def _config_latex_tool(self, lt):
        Operation._config_latex_tool(self, lt)
        if not 'mathtools' in lt.packages:
            lt.packages.append('mathtools')
                
    def formatted(self, format_type, fence=False):
        formatted_label = self.label.formatted(format_type, fence=False)
        formatted_size = self.size.formatted(format_type, fence=False)
        if format_type == LATEX:
            return r'\prescript{}{' + formatted_size + r'}\langle ' + formatted_label + r' \rvert'
        else:
            return '{' + formatted_size + '}_<'+formatted_label+'|'

REGISTER_BRA = Literal(pkg, 'REGISTER_BRA', operation_maker = lambda operands : RegisterBra(*operands))

class RegisterKet(Operation):
    def __init__(self, label, size):
        Operation.__init__(self, REGISTER_KET, [label, size])
        self.label = label
        self.size = size # size of the register
    
    def formatted(self, format_type, fence=False, no_lvert=False):
        formatted_label = self.label.formatted(format_type, fence=False)
        formatted_size = self.size.formatted(format_type, fence=False)
        left_str = r'\lvert ' if format_type == LATEX else '|'
        if no_lvert: left_str = ''
        if format_type == LATEX:
            return left_str + formatted_label + r' \rangle_{' + formatted_size + '}'
        else:
            return left_str + formatted_label + '>_{' + formatted_size + '}'

REGISTER_KET = Literal(pkg, 'REGISTER_KET', operation_maker = lambda operands : RegisterKet(*operands))
    
class Meas(Operation):
    def __init__(self, ket):
        Operation.__init__(self, MEAS, ket)
        self.ket = ket
    
MEAS = Literal(pkg, 'MEAS', {LATEX: r'{\cal M}'}, operation_maker = lambda operands : Meas(*operands))

