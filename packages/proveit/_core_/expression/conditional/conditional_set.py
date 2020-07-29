from proveit._core_.expression.label.literal import Literal
from proveit._core_.expression.operation import Operation

class ConditionalSet(Operation):
    # operator of the ConditionalSet operation
    _operator_ = Literal(stringFormat='CondSet', 
                         latexFormat=r'\textrm{CondSet}', context=__file__)   
    
    def __init__(self, conditionals):
        Operation.__init__(ConditionalSet._operator_, conditionals)
        self.conditionals = self.operands
    
    def string(self, **kwargs):
        inner_str = '; '.join(conditional.string(fence=False) \
                              for conditional in zip(self.conditionals))
        return '{' + inner_str +'.'
    
    def latex(self, **kwargs):
        inner_str = r' \\ '.join(conditional.latex(fence=False) \
                                  for conditional in zip(self.conditionals))
        inner_str = r'\begin{array}{ccc}' + inner_str + r'\end{array}'
        inner_str = r'\left\{' + inner_str + r'\right..'
        return inner_str
