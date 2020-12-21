from proveit.expression import Literal, Operation, LATEX

pkg = __package__


class AngDiff(Operation):
    def __init__(self, angle1, angle2):
        Operation.__init__(self, ANGULAR_DIFFERENCE, (angle1, angle2))
        self.angle1 = angle1
        self.angle2 = angle2


ANGULAR_DIFFERENCE = Literal(
    pkg, 'AngDiff', {
        LATEX: r'{\rm AngDiff}'}, operation_maker=lambda operands: AngDiff(
            *operands))
