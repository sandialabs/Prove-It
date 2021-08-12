import os
from inspect import signature
from .label import Label
from .var import Variable

class Literal(Label):
    """
    A Literal expresses contextual meaning.  Such Labels are not interchangeable.
    The Literal must be associated with a 'theory' that should be the name of a package.
    Through Axiom elimination, a Literal may be converted to the Variable with the same
    label.
    """

    instances = dict()  # map style information to Literal instances.

    @staticmethod
    def _clear_():
        '''
        Clear all references to Prove-It information under
        the Expression jurisdiction.  All Expression classes that store Prove-It
        state information must implement _clear_ to clear that information.
        '''
        Literal.instances.clear()

    def __init__(self, string_format, latex_format=None, *,
                 extra_core_info=tuple(), theory=None,
                 fence_when_forced=False, styles=None):
        '''
        Create a Literal.  If latex_format is not supplied, the
        string_format is used for both.  The Literal will be stored
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
                theory = Theory.get_theory(theory)
        Label.__init__(
            self, string_format, latex_format, 'Literal',
            tuple(extra_core_info) + (theory.name,), styles=styles,
            fence_when_forced=fence_when_forced)
        self.theory = theory
        # if self._core_info in Literal.instances:
        #    raise DuplicateLiteralError("Only allowed to create one Literal with the same theory and string/latex formats")
        Literal.instances.setdefault(self._style_id, self)

    @classmethod
    def instance(literal_class, theory, string_format, latex_format):
        raise NotImplementedError(
            "'instance' method has not been implemented for a Literal of type %s" %
            str(literal_class))

    def as_variable(self):
        '''
        Return the var with the same label as this Literal.
        '''
        return Variable(self.string_format, self.latex_format)

    @classmethod
    def _make(literal_class, core_info, sub_expressions, *, styles):
        '''
        Make the object of class `literal_class` matching the core information
        and sub expressions.
        '''
        from proveit import Theory
        if len(sub_expressions) > 0:
            raise ValueError('Not expecting any sub_expressions of Literal')
        if len(core_info) < 4:
            raise ValueError(
                "Expecting " +
                literal_class.__name__ +
                " core_info to contain at least 4 items: '" +
                literal_class.__name__ +
                "', string_format, latex_format, and the theory")
        if core_info[0] != 'Literal':
            raise ValueError("Expecting core_info[0] to be 'Literal'")
        core_info = tuple(core_info)  # make it hashable

        # If the Literal is not in the instances dictionary, just make it independently
        # without storing it in the instances dictionary.  This allows us to create
        # Expression objects out of the __pv_it database without causing
        # a DuplicateLiteralError.
        string_format, latex_format = core_info[1:3]
        if core_info[3] == 'fence_when_forced':
            fence_when_forced = True
            extra_core_info = core_info[4:-1]
        else:
            fence_when_forced = False
            extra_core_info = core_info[3:-1]
        theory = Theory.get_theory(core_info[-1])
        prev_theory_default = Theory.default
        Theory.default = theory
        try:
            if len(extra_core_info) > 0:
                # If there is extra core information, we need to call
                # a make_literal method.
                if hasattr(literal_class, 'make_literal'):
                    made_obj = literal_class.make_literal(
                        string_format, latex_format, 
                        extra_core_info=extra_core_info,
                        theory=theory, styles=styles)
                else:
                    raise NotImplementedError(
                        "Must implement the 'make_literal(string_format, "
                        "latex_format, *, extra_core_info, theory, styles)' "
                        "static method for class %s which uses "
                        "'extra_core_info'"%str(literal_class))
            elif literal_class == Literal:
                made_obj = Literal(
                    string_format, latex_format, 
                    extra_core_info=extra_core_info, theory=theory,
                    fence_when_forced=fence_when_forced, styles=styles)
            else:
                sig = signature(literal_class.__init__)
                kwargs = dict()
                for param in sig.parameters:
                    if param == 'string_format':
                        kwargs['string_format'] = string_format
                    elif param == 'latex_format':
                        kwargs['latex_format'] = latex_format
                    elif param == 'fence_when_forced':
                        kwargs['fence_when_forced'] = fence_when_forced
                    elif param == 'theory':
                        kwargs['theory'] = theory
                # styles are mandatory keyword argument
                kwargs['styles'] = styles
                made_obj = literal_class(**kwargs)
        finally:
            Theory.default = prev_theory_default  # restore the default

        if made_obj._style_id in Literal.instances:
            # We can use the pre-existing instance.
            return Literal.instances[made_obj._style_id]
        return made_obj


class DuplicateLiteralError(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message
