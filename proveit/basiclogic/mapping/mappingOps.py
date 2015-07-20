from proveit.expression import Operation, Literal

pkg = __package__

class Domain(Operation):
    def __init__(self, mapExpr):
        Operation.__init__(self, DOMAIN, [mapExpr])
DOMAIN = Literal(pkg, 'DOMAIN', lambda operand : Domain(operand))

class CoDomain(Operation):
    def __init__(self, mapExpr):
        Operation.__init__(self, CODOMAIN, [mapExpr])
CODOMAIN = Literal(pkg, 'CODOMAIN', lambda operand : CoDomain(operand))
