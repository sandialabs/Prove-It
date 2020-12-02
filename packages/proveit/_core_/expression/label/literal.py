import os
from .label import Label
from .var import Variable

class Literal(Label):
    """
    A Literal expresses contextual meaning.  Such Labels are not interchangeable.
    The Literal must be associated with a 'theory' that should be the name of a package.
    Through Axiom elimination, a Literal may be converted to the Variable with the same
    label.
    """
    
    instances = dict() # map core information to Literal instances
    
    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information under
        the Expression jurisdiction.  All Expression classes that store Prove-It
        state information must implement _clear_ to clear that information.
        '''
        Literal.instances.clear()
        
    def __init__(self, stringFormat, latexFormat=None, extraCoreInfo=tuple(), theory=None, styles=None):
        '''
        Create a Literal.  If latexFormat is not supplied, the 
        stringFormat is used for both.  The Literal will be stored
        in the 'common' folder of its theory.  For this reason, it
        is important that the _common__ notebook imports all of the
        Literal's that belong to it (which will typically be done
        without any extra effort); otherwise, it will have to be
        recreated each session.
        '''
        from proveit._core_.theory import Theory
        if theory is None:
            # use the default
            theory = Theory.default
            if theory is None:
                # if no default is specified; use the current working 
                # directory
                theory = Theory()
        elif isinstance(theory, str):
            # convert a path string to a Theory
            if os.path.exists(theory):
                # Make a Theory given a path.
                theory = Theory(theory)
            else:
                # Make a Theory given a name.
                # First create the local theory to make sure we have access 
                # to theory roots referenced by this theory.
                Theory() 
                theory = Theory.getTheory(theory)
        Label.__init__(self, stringFormat, latexFormat, 'Literal', (theory.name,)+tuple(extraCoreInfo),
                       styles=styles)
        self.theory = theory
        #if self._coreInfo in Literal.instances:
        #    raise DuplicateLiteralError("Only allowed to create one Literal with the same theory and string/latex formats")
        Literal.instances[self._coreInfo] = self
    
    @classmethod
    def instance(literalClass, theory, stringFormat, latexFormat):
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
        from proveit import Theory
        import inspect
        if len(subExpressions) > 0:
            raise ValueError('Not expecting any subExpressions of Literal')
        if len(coreInfo) < 4:
            raise ValueError("Expecting " + literalClass.__name__ + " coreInfo to contain at least 4 items: '" + literalClass.__name__ + "', stringFormat, latexFormat, and the theory")
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
            theory = Theory.getTheory(coreInfo[3])
            prev_theory_default = Theory.default
            Theory.default = theory
            try:
                extra_core_info = coreInfo[4:]
                init_args = inspect.getargspec(literalClass.__init__)[0]
                kwargs = dict()
                if 'theory' in init_args: kwargs['theory'] = theory
                if 'styles' in init_args: kwargs['styles'] = styles
                if len(extra_core_info) > 0:
                    # If there is extra core information, we need to call
                    # a makeLiteral method.
                    if hasattr(literalClass, 'makeLiteral'):
                        made_obj = literalClass.makeLiteral(string_format, latex_format, 
                                                            extra_core_info, theory)
                    else:
                        raise NotImplementedError("Must implement the 'makeLiteral(string_format, latex_format, extra_core_info, theory)' static method for class %s which uses 'extra_core_info'"%str(literalClass))
                elif literalClass==Literal:
                    made_obj = Literal(string_format, latex_format, extra_core_info, theory)
                elif len(init_args)==1:
                    made_obj = literalClass() # no arguments (except self) are taken
                elif len(init_args)==2 and init_args[1]=='stringFormat' and coreInfo[1]==coreInfo[2]:
                    made_obj = literalClass(string_format, theory)
                elif len(init_args)>=3 and init_args[1]=='stringFormat' and init_args[2]=='latexFormat':
                    made_obj = literalClass(string_format, latex_format, **kwargs)
                else:
                    made_obj = literalClass(**kwargs)
            finally:
                Theory.default = prev_theory_default # restore the default
            
            Literal.instances.pop(coreInfo)
            return made_obj.withStyles(**styles)

    def remakeArguments(self):
        '''
        Yield the argument values that could be used to recreate the
        Literal.
        '''
        import inspect
        init_args = inspect.getargspec(self.__class__.__init__)[0]
        if len(init_args)==1:
            return # nothing needed
        for arg in Label.remakeArguments(self):
            yield arg
        if len(init_args)==3:
            return # nothing more
        if (len(init_args)==6 and init_args[3]=='extraCoreInfo' \
                and init_args[4]=='theory' and init_args[5]=='styles'):
            core_info = self.coreInfo()
            theory_name = core_info[3]
            extra_core_info = core_info[4:]
            if len(extra_core_info) > 0:
                yield ('extraCoreInfo', extra_core_info)
            yield ('theory', '"' + theory_name + '"')
        else:
            raise NotImplementedError("Must properly implement the "
                                      "'remakeArguments' method for "
                                      "class %s"%str(self.__class__))
        

class DuplicateLiteralError(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message

