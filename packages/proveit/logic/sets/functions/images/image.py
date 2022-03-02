from proveit import Operation, Function, Literal, Lambda, equality_prover
from proveit import f, A

class Image(Operation):
    '''
    Represents the image of a set under a function (operator) which
    is the set obtained by applying the function to each element of
    the original set.
    '''
    _operator_ = Literal('IMAGE', theory=__file__)
    
    def __init__(self, elem_function, set_of_elems, *, styles=None):
        Operation.__init__(self, Image._operator_, 
                           (elem_function, set_of_elems),
                           styles=styles)
        self.elem_function = elem_function
        self.set_of_elems = set_of_elems
    
    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        If the function is a Lambda map, simplify the Image via
        its definition.
        '''
        if isinstance(self.elem_function, Lambda):
            return self.definition()
        return Operation.shallow_simplification(
                self, must_evaluate=must_evaluate)        

    @equality_prover('defined', 'define')
    def definition(self, **defaults_config):
        from . import set_image_def
        return set_image_def.instantiate(
                {f:self.elem_function, A:self.set_of_elems})
        
    def string(self, **kwargs):
        formatted_fn = self.elem_function.string(fence=True)
        formatted_set = self.set_of_elems.string(fence=False)
        return '%s^*(%s)'%(formatted_fn, formatted_set)

    def latex(self, **kwargs):
        formatted_fn = self.elem_function.latex(fence=True)
        formatted_set = self.set_of_elems.latex(fence=False)
        return r'%s^{\rightarrow}(%s)'%(formatted_fn, formatted_set)
