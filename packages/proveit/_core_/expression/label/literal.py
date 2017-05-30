from label import Label
from var import Variable

class Literal(Label):
    """
    A Literal expresses contextual meaning.  Such Labels are not interchangeable.
    The Literal must be associated with a 'context' that should be the name of a package.
    Through Axiom elimination, a Literal may be converted to the Variable with the same
    label.
    """
    
    instances = dict() # map core information to Literal instances
    
    def __init__(self, stringFormat, latexFormat=None, context=None):
        '''
        Create a Lateral.  If latexFormat is not supplied, the stringFormat is used for both.
        '''
        from proveit import Context
        if context is None:
            context = Context()
        elif isinstance(context, str):
            # convert a path string to a Context
            context = Context(context)
        self.context = context
        Label.__init__(self, stringFormat, latexFormat, 'Literal', [context.name])
        if self._coreInfo in Literal.instances:
            raise DuplicateLiteralError("Only allowed to create one Literal with the same context and string/latex formats")
        Literal.instances[self._coreInfo] = self
        '''
        if self.context is None or self.context[:7] != 'proveit':
            raise Exception('Literal package must be contained within proveit.  This may result from a relative import.\nUse absolute imports with proveit Literals.')
        '''
    
    @classmethod
    def instance(literalClass, context, stringFormat, latexFormat):
        raise NotImplementedError("'instance' method has not been implemented for a Literal of type %s"%str(literalClass))
    
    def asVariable(self):
        '''
        Return the var with the same label as this Literal.
        '''
        return Variable(self.stringFormat, self.latexFormat)
    
    @classmethod
    def make(literalClass, coreInfo, subExpressions):
        from proveit import Context
        if len(subExpressions) > 0:
            raise ValueError('Not expecting any subExpressions of Literal')
        if len(coreInfo) != 4:
            raise ValueError("Expecting " + literalClass.__name__ + " coreInfo to contain 4 items: '" + literalClass.__name__ + "', stringFormat, latexFormat, and the context")
        if coreInfo[0] != 'Literal':
            raise ValueError("Expecting coreInfo[0] to be 'Literal'")
        coreInfo = tuple(coreInfo) # make it hashable
        try:
            return Literal.instances[coreInfo]
        except KeyError:
            # If the Literal is not in the instances dictionary, just make it independently
            # without storing it in the instances dictionary.  This allows us to create
            # Expression objects out of the _pv_it_ database without causing
            # a DuplicateLiteralError.
            context = Context.getContext(coreInfo[3])
            madeObj = literalClass(coreInfo[1], coreInfo[2], context)
            Literal.instances.pop(coreInfo)
            return madeObj

class DuplicateLiteralError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
