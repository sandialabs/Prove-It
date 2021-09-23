from proveit.abstract_algebra import GroupAdd

class FieldAdd(GroupAdd):
    def __init__(self, operator, operands, *, styles=None):
        return GroupAdd.__init__(self, operator, operands, styles=styles)
