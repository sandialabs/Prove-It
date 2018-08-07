from .label import Label
from .var import Variable

class Literal(Label):
    """
    A Literal expresses contextual meaning.  Such Labels are not interchangeable.
    The Literal must be associated with a 'context' that should be the name of a package.
    Through Axiom elimination, a Literal may be converted to the Variable with the same
    label.
    """
    
    instances = dict() # map core information to Literal instances
    
    def __init__(self, stringFormat, latexFormat=None, extraCoreInfo=tuple(), context=None):
        '''
        Create a Literal.  If latexFormat is not supplied, the stringFormat is used for both.
        '''
        from proveit._core_.context import Context
        from proveit._core_.expression.expr import Expression
        if context is None:
            # use the default
            context = Context.default
            if context is None:
                # if no default is specified; use the current working directory
                context = Context()
        elif isinstance(context, str):
            # convert a path string to a Context
            context = Context(context)
        self.context = context
        Label.__init__(self, stringFormat, latexFormat, 'Literal', (context.name,)+tuple(extraCoreInfo))
        #if self._coreInfo in Literal.instances:
        #    raise DuplicateLiteralError("Only allowed to create one Literal with the same context and string/latex formats")
        Literal.instances[self._coreInfo] = self
        Expression.contexts[self] = self.context
    
    @classmethod
    def instance(literalClass, context, stringFormat, latexFormat):
        raise NotImplementedError("'instance' method has not been implemented for a Literal of type %s"%str(literalClass))
    
    def asVariable(self):
        '''
        Return the var with the same label as this Literal.
        '''
        return Variable(self.stringFormat, self.latexFormat)
    
    @classmethod
    def _make(literalClass, coreInfo, styles, subExpressions):
        '''
        Make the object of class `literalClass` matching the core information
        and sub expressions.
        '''
        from proveit import Context
        import inspect
        if len(subExpressions) > 0:
            raise ValueError('Not expecting any subExpressions of Literal')
        if len(coreInfo) < 4:
            raise ValueError("Expecting " + literalClass.__name__ + " coreInfo to contain at least 4 items: '" + literalClass.__name__ + "', stringFormat, latexFormat, and the context")
        if coreInfo[0] != 'Literal':
            raise ValueError("Expecting coreInfo[0] to be 'Literal'")
        coreInfo = tuple(coreInfo) # make it hashable
        if coreInfo in Literal.instances:
            return Literal.instances[coreInfo].withStyles(**styles)
        else:
            # If the Literal is not in the instances dictionary, just make it independently
            # without storing it in the instances dictionary.  This allows us to create
            # Expression objects out of the __pv_it database without causing
            # a DuplicateLiteralError.
            string_format, latex_format = coreInfo[1:3]
            context = Context.getContext(coreInfo[3])
            Context.default = context
            extra_core_info = coreInfo[4:]
            init_args = inspect.getargspec(literalClass.__init__)[0]
            if literalClass==Literal:
                made_obj = Literal(string_format, latex_format, extra_core_info, context)
            elif len(init_args)==1:
                made_obj = literalClass() # no arguments (except self) are taken
            elif len(init_args)==2 and init_args[1]=='stringFormat' and coreInfo[1]==coreInfo[2]:
                made_obj = literalClass(string_format, context)
            elif len(init_args)==3 and init_args[1]=='stringFormat' and init_args[2]=='latexFormat':
                made_obj = literalClass(string_format, latex_format)
            elif len(init_args)==4 and init_args[1]=='stringFormat' and init_args[2]=='latexFormat' and init_args[3]=='context':
                made_obj = literalClass(string_format, latex_format, context)
            elif hasattr(literalClass, 'makeLiteral'):
                if len(extra_core_info)==0:
                    made_obj = literalClass.makeLiteral(string_format, latex_format, context)
                else:
                    made_obj = literalClass.makeLiteral(string_format, latex_format, extra_core_info, context)
            else:
                raise NotImplementedError("Must implement the 'makeLiteral(string_format, latex_format, context)' static method for class %s"%str(literalClass)) 
                
            Literal.instances.pop(coreInfo)
            return made_obj.withStyles(**styles)
        

class DuplicateLiteralError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

