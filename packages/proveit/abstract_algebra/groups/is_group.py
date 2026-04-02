from proveit import Literal, ClassMembership

class IsGroup(ClassMembership):
    '''
    A Groups expression denotes the class of sets that are groups
    under a particular group operation.
    '''
    
    _operator_ = Literal(
            string_format=r'IsGroup', latex_format=r'\textrm{IsGroup}',
            theory=__file__)
    
    def __init__(self, collection, group_operator, *, styles=None):
        ClassMembership.__init__(self, IsGroup._operator_, 
                                 collection, group_operator, 
                                 styles=styles)
        self.collection = collection
        self.group_operator = group_operator

    def formatted_class(self, format_type):
        formatted_op = self.group_operator.formatted(format_type, fence=False)
        if format_type == 'latex':
            return r'{\rm Group}(%s)'%formatted_op
        return r'Group(%s)'%formatted_op