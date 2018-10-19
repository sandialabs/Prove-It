from proveit import Operation, Literal, USE_DEFAULTS
from proveit._common_ import a, b, c, d, e, f, g, h, i, x, y

class Len(Operation):
    # operator of the Length operation.
    _operator_ = Literal(stringFormat='length', context=__file__)   
    
    def __init__(self, operand):
        Operation.__init__(self, Len._operator_, operand)
        if not hasattr(self, 'operand'):
            self.operand = self.operands # always only one operand that may be a list
        
    @staticmethod
    def extractInitArgValue(argName, operator_or_operators, operand_or_operands):
        if argName=='operand':
            return operand_or_operands
        
    def string(self, **kwargs):
        return '|' + self.operand.string() + '|'
    
    def latex(self, **kwargs):
        return '|' + self.operand.latex() + '|'
    
    def evaluation(self, assumptions=USE_DEFAULTS):
        from proveit.logic import Equals
        from ._axioms_ import listLen0, listLenDef
        from proveit.number.numeral.decimal._theorems_ import listLen1, listLen2, listLen3, listLen4, listLen5
        from proveit.number.numeral.decimal._theorems_ import listLen6, listLen7, listLen8, listLen9
        if len(self.operands) == 0:
            return listLen0
        elif len(self.operands) == 1:
            return listLen1.specialize({a:self.operands[0]})
        elif len(self.operands) == 2:
            a_, b_ = self.operands
            return listLen2.specialize({a:a_, b:b_})
        elif len(self.operands) == 3:
            a_, b_, c_ = self.operands
            return listLen3.specialize({a:a_, b:b_, c:c_})
        elif len(self.operands) == 4:
            a_, b_, c_, d_ = self.operands
            return listLen4.specialize({a:a_, b:b_, c:c_, d:d_})
        elif len(self.operands) == 5:
            a_, b_, c_, d_, e_ = self.operands
            return listLen5.specialize({a:a_, b:b_, c:c_, d:d_, e:e_})
        elif len(self.operands) == 6:
            a_, b_, c_, d_, e_, f_ = self.operands
            return listLen6.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_})
        elif len(self.operands) == 7:
            a_, b_, c_, d_, e_, f_, g_ = self.operands
            return listLen7.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_, g:g_})
        elif len(self.operands) == 8:
            a_, b_, c_, d_, e_, f_, g_, h_ = self.operands
            return listLen8.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_, g:g_, h:h_})
        elif len(self.operands) == 9:
            a_, b_, c_, d_, e_, f_, g_, h_, i_ = self.operands
            return listLen9.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_, g:g_, h:h_, i:i_})
        else:
            equiv = listLenDef.specialize({x:self.operands[:-1], y:self.operands[-1]})
            value = equiv.rhs.evaluation(assumptions).rhs
            return Equals(self, value).prove(assumptions)
