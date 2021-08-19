from proveit import Operation

class FieldMult(Operation):
    def __init__(self, operator, operands, *, styles=None):
        return Operation.__init__(self, operator, operands, styles=styles)
    