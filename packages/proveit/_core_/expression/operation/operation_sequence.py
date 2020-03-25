from .operation import Operation

class OperationSequence(Operation):
    def __init__(self, operators, operands, styles=None):
        from proveit import Iter
        if len(operands) != len(operators)+1:
            raise ValueError("An operation sequence must have one more operand than operators")
        operand_iter_indices = set()
        for k, operator in enumerate(operators):
            if isinstance(operator, Iter):
                operand_idx = k if isinstance(operands[k], Iter) else k+1
                operand_iter_indices.add(operand_idx)
                operand = operands[operand_idx]
                if not isinstance(operand, Iter):
                    raise ValueError("In an operation sequence, an iteration of operations must correspond with an iteration of operands (with iterated operands preceeding operation or vice-versa)")
                if operand.start_index != operator.start_index or operand.end_index != operator.end_index:
                    raise ValueError("In an operation sequence, an operation and operand iterations in correspondence must have the same start and end indices")
        for k, operand in enumerate(operands):
            if isinstance(operand, Iter) and k not in operand_iter_indices:
                    raise ValueError("In an operation sequence, an iteration of operands must correspond with an iteration of operations (with iterated operands preceeding operation or vice-versa)")                
        Operation.__init__(self, operators, operands, styles=styles)
    
    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)
