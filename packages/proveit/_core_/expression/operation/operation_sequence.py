from .operation import Operation

class OperationSequence(Operation):
    def __init__(self, operators, operands, styles=dict(), requirements=tuple()):
        from proveit import Iter
        if len(operands) != len(operators)+1:
            raise ValueError("An operation sequence must have one more operand than operators")
        operand_iter_indices = set()
        for k, operator in enumerate(operators):
            if isinstance(operator, Iter):
                if operator.ndims != 1:
                    raise ValueError("An iteration in an operation sequence may only be 1 dimensional")
                operand_idx = k if isinstance(operands[k], Iter) else k+1
                operand_iter_indices.add(operand_idx)
                operand = operands[operand_idx]
                if not isinstance(operand, Iter):
                    raise ValueError("In an operation sequence, an iteration of operations must correspond with an iteration of operands (with iterated operands preceeding operation or vice-versa)")
                if operand.ndims != 1:
                    raise ValueError("An iteration in an operation sequence may only be 1 dimensional")
                if operand.start_index != operator.start_index or operand.end_index != operator.end_index:
                    raise ValueError("In an operation sequence, an operation and operand iterations in correspondence must have the same start and end indices")
        for k, operand in enumerate(operands):
            if isinstance(operand, Iter) and k not in operand_iter_indices:
                    raise ValueError("In an operation sequence, an iteration of operands must correspond with an iteration of operations (with iterated operands preceeding operation or vice-versa)")                
        Operation.__init__(self, operators, operands, styles=styles, requirements=requirements)
    
    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)
    
    def _formatted(self, formatType, **kwargs):
        '''
        When there are multiple operators, the default formatting assumes there is one more operator than operands
        and the operators should come between successive operands.
        '''
        from proveit import Iter
        from proveit._core_.expression.fencing import maybeFenced
        fence =  kwargs['fence'] if 'fence' in kwargs else False
        subFence =  kwargs['subFence'] if 'subFence' in kwargs else True
        ellipses = r'\ldots' if formatType=='latex' else '...'
        inner_str = ''
        formatted_operators = []
        formatted_operands = []
        for operator in self.operators:
            if isinstance(operator, Iter):
                formatted_operators += [operator.first().formatted(formatType), ellipses, operator.last().formatted(formatType)]
            else: formatted_operators.append(operator.formatted(formatType))
        for operand in self.operands:
            if isinstance(operand, Iter):
                formatted_operands += [operand.first().formatted(formatType, fence=subFence), '', operand.last().formatted(formatType, fence=subFence)]
            else: formatted_operands.append(operand.formatted(formatType, fence=subFence))
        inner_str = ' '.join(formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in zip(formatted_operands, formatted_operators)) + ' ' + formatted_operands[-1]
        return maybeFenced(formatType, inner_str, fence=fence)
