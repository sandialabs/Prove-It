from proveit import Literal, ClassMembership

class IsField(ClassMembership):
    '''
    A Fields expression denotes the class of sets that are rings
    under particular "addition" and "multiplication" operations.
    '''
    
    _operator_ = Literal(
            string_format=r'IsField', latex_format=r'\textrm{IsField}',
            theory=__file__)
    
    def __init__(self, collection, add_operator, mult_operator, *, styles=None):
        ClassMembership.__init__(self, IsField._operator_, 
                                 collection, add_operator, mult_operator,
                                 styles=styles)
        self.collection = collection
        self.add_operator = add_operator
        self.mult_operator = mult_operator

    def formatted_class(self, format_type):
        formatted_add = self.add_operator.formatted(format_type, fence=False)
        formatted_mult = self.mult_operator.formatted(format_type, fence=False)
        if format_type == 'latex':
            return r'{\rm Field}(%s, %s)'%(formatted_add, formatted_mult)
        return r'Field(%s, %s)'%(formatted_add, formatted_mult)

def is_rational_field(collection):
    from proveit.numbers import Rational
    return IsField(collection, Rational)

def is_real_field(collection):
    from proveit.numbers import Real
    return IsField(collection, Real)

def is_complex_field(collection):
    from proveit.numbers import Complex
    return IsField(collection, Complex)
