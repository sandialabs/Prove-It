from proveit import Literal, ClassMembership

class IsRing(ClassMembership):
    '''
    A Rings expression denotes the class of sets that are rings
    under particular "addition" and "multiplication" operations.
    '''
    
    _operator_ = Literal(
            string_format=r'IsRing', latex_format=r'\textrm{IsRing}',
            theory=__file__)
    
    def __init__(self, collection, add_operator, mult_operator, *,
                 styles=None):
        ClassMembership.__init__(self, IsRing._operator_, 
                                 collection, add_operator, mult_operator,
                                 styles=styles)
        self.collection = collection
        self.add_operator = add_operator
        self.mult_operator = mult_operator

    def formatted_class(self, format_type):
        formatted_add = self.add_operator.formatted(format_type, fence=False)
        formatted_mult = self.mult_operator.formatted(format_type, fence=False)
        if format_type == 'latex':
            return r'{\rm Ring}(%s, %s)'%(formatted_add, formatted_mult)
        return r'Ring(%s, %s)'%(formatted_add, formatted_mult)