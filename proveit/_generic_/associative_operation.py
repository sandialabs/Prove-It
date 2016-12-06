from proveit import Operation, ExpressionList, Etcetera

class AssociativeOperation(Operation):
    def __init__(self, operator, *operands):
        '''
        Represent an associative operator operating on any number of operands.
        '''
        Operation.__init__(self, operator, operands)   
        assert isinstance(self.operands, ExpressionList)
    
    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)
    
    def _formatted(self, formatType, **kwargs):
        '''
        Format the associative operation in the form "A * B * C" where '*' is a stand-in for
        the operator that is obtained from self.operator.formatted(formatType).
        '''
        # Different formatting when there is 0 or 1 element, unless it is an Etcetera
        if len(self.operands) < 2:
            if len(self.operands) == 0 or not isinstance(self.operands[0], Etcetera):
                if formatType == 'string':
                    return Operation.string(self, **kwargs)
                elif formatType == 'latex':
                    return Operation.latex(self, **kwargs)
                raise ValueError("Unexpected formatType: " + str(formatType))  
        fence =  kwargs['fence'] if 'fence' in kwargs else False
        subFence =  kwargs['subFence'] if 'subFence' in kwargs else True
        formattedOperator = self.operator.formatted(formatType) 
        return self.operands.formatted(formatType, fence=fence, subFence=subFence, formattedOperator=formattedOperator)
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
