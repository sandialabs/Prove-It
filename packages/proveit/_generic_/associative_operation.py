from proveit import Operation, ExprList, Iter

class AssociativeOperation(Operation):
    def __init__(self, operator, *operands):
        '''
        Represent an associative operator operating on any number of operands.
        '''
        if len(operands)==1 and isinstance(operands[0], Iter):
            operand_or_operands = operands[0]
        else:
            operand_or_operands = operands
        Operation.__init__(self, operator, operand_or_operands)   
    
    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)
    
    def _formatted(self, formatType, **kwargs):
        '''
        Format the associative operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.operator.formatted(formatType).
        '''
        # Different formatting when there is 0 or 1 element, unless it is an Iter
        if len(self.operands) < 2:
            if len(self.operands) == 0 or not isinstance(self.operands[0], Iter):
                if formatType == 'string':
                    return '[' + self.operator.string(fence=True) +  '](' + self.operands.string(fence=False, subFence=False) + ')'
                else:
                    return '\left[' + self.operator.latex(fence=True) +  r'\right]\left(' + self.operands.latex(fence=False, subFence=False) + r'\right)'
                raise ValueError("Unexpected formatType: " + str(formatType))  
        fence =  kwargs['fence'] if 'fence' in kwargs else False
        subFence =  kwargs['subFence'] if 'subFence' in kwargs else True
        formattedOperator = ' ' + self.operator.formatted(formatType) + ' '
        return self.operand_or_operands.formatted(formatType, fence=fence, subFence=subFence, formattedOperator=formattedOperator)
        """
        outStr = ''
        # insert ellipses (two dots in our case) before and after Etcetera expressions
        formattedOperands = [] 
        for operand in self.operands:
            if isinstance(operand, Etcetera):
                if len(formattedOperands) > 0 and formattedOperands[-1] == '..' + spc:
                    # instead of having "..  .." back-to-back, do ".."
                    formattedOperands[-1] = '...'
                else:
                    formattedOperands.append(spc + '..')
                formattedOperands.append(operand.bundledExpr.formatted(formatType, fence=subFence))
                formattedOperands.append('..' + spc)
            else:
                formattedOperands.append(operand.formatted(formatType, fence=subFence))
        # put the formatted operator between each of formattedOperands
        if formatType == STRING:
            if fence: outStr += '('
            outStr += (' ' + self.operator.formatted(formatType) + ' ').join(formattedOperands)
            if fence: outStr += ')'
        elif formatType == LATEX:
            if fence: outStr += r'\left('
            outStr += (' ' + self.operator.formatted(formatType) + ' ').join(formattedOperands)
            if fence: outStr += r'\right)'
        return outStr           
        """
