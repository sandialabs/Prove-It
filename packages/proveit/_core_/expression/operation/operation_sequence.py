from .operation import Operation


class OperationSequence(Operation):
    def __init__(self, operators, operands, styles=None):
        from proveit import ExprRange
        if len(operands) != len(operators) + 1:
            raise ValueError(
                "An operation sequence must have one more operand than operators")
        operand_range_indices = set()
        for k, operator in enumerate(operators):
            if isinstance(operator, ExprRange):
                operand_idx = k if isinstance(
                    operands[k], ExprRange) else k + 1
                operand_range_indices.add(operand_idx)
                operand = operands[operand_idx]
                if not isinstance(operand, ExprRange):
                    raise ValueError(
                        "In an operation sequence, an range of operations must correspond with a range of operands (with operands preceeding operations or vice-versa)")
                if operand.start_index != operator.start_index or operand.end_index != operator.end_index:
                    raise ValueError(
                        "In an operation sequence, operation and operand ranges in correspondence must have the same start and end indices")
        for k, operand in enumerate(operands):
            if isinstance(
                    operand,
                    ExprRange) and k not in operand_range_indices:
                raise ValueError(
                    "In an operation sequence, an iteration of operands must correspond with an iteration of operations (with iterated operands preceeding operation or vice-versa)")
        Operation.__init__(self, operators, operands, styles=styles)

    def string(self, **kwargs):
        return self._formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self._formatted('latex', **kwargs)
