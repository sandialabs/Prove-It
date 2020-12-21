from proveit.expression import Operation, Literal

pkg = __package__


class Domain(Operation):
    def __init__(self, map_expr):
        Operation.__init__(self, DOMAIN, [map_expr])


DOMAIN = Literal(pkg, 'DOMAIN', lambda operand: Domain(operand))


class CoDomain(Operation):
    def __init__(self, map_expr):
        Operation.__init__(self, CODOMAIN, [map_expr])


CODOMAIN = Literal(pkg, 'CODOMAIN', lambda operand: CoDomain(operand))
