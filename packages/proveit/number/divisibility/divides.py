from proveit import Context, Operation, Literal

class Divides(Operation):
    
    context = Context('.')
    _operator_ = Literal('|', context=context)
    
    def __init__(self, a, b):
        Operation.__init__(self, Divides._operator_, [a, b])