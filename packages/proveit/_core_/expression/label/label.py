import re
from inspect import signature
from proveit._core_.expression.expr import Expression
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_.expression.fencing import (
    maybe_fenced_string, maybe_fenced_latex)

class Label(Expression):
    """
    Label is the base class for the Variable, Literal, and Multi_variable expr
    classes (Label is not itself an expr class).  It is a mathematical label
    with string and latex formatting.
    """

    def __init__(self, string_format, latex_format=None,
                 label_type='Label', extra_core_info=tuple(), *,
                 fence_when_forced=False, styles=None):
        '''
        Create a Label with the given string and latex formatting.
        By default, the latex formatting is the same as the string formatting.
        '''
        self.string_format = string_format
        if latex_format is None:
            latex_format = string_format
        self.latex_format = latex_format.strip(
        ) if latex_format is not None else string_format
        assert re.match(
            '[!-~]+', self.string_format), 'Label string_format may include only printable ascii characters and no space'
        assert re.match(
            '[ -~]+', self.latex_format), 'Label latex_format may include only printable ascii characters'
        if not isinstance(self.string_format, str):
            raise TypeError("'string_format' must be a str")
        if not isinstance(self.latex_format, str):
            raise TypeError("'latex_format' must be a str")
        if ',' in self.string_format or ',' in self.latex_format:
            raise ValueError("Comma not allowed within a label's formatting")
        if fence_when_forced:
            extra_core_info = ('fence_when_forced',) + extra_core_info
        core_info = ((label_type, self.string_format, self.latex_format) + 
                     extra_core_info)
        self.fence_when_forced = fence_when_forced
        Expression.__init__(self, core_info, sub_expressions=tuple(),
                            styles=styles)

    def string(self, **kwargs):
        '''
        Return a string representation of the Label.
        '''
        if self.fence_when_forced:
            kwargs['fence'] = (kwargs['force_fence'] if 'force_fence' in
                               kwargs else False)
            return maybe_fenced_string(self.string_format, **kwargs)
        return self.string_format

    def latex(self, **kwargs):
        '''
        Return a latex representation of the Label.
        '''
        if self.fence_when_forced:
            kwargs['fence'] = (kwargs['force_fence'] if 'force_fence' in
                               kwargs else False)
            return maybe_fenced_latex(self.latex_format, **kwargs)
        return self.latex_format

    @classmethod
    def _make(label_class, core_info, sub_expressions, *, styles):
        if len(sub_expressions) > 0:
            raise ValueError('Not expecting any sub_expressions of Label')
        fence_when_forced = False
        if len(core_info) == 4 and core_info[3] == 'fence_when_forced':
                fence_when_forced = True
        elif len(core_info) != 3:
            raise ValueError(
                "Expecting " + label_class.__name__ +
                " core_info to contain 3 items: '" +
                label_class.__name +
                "', string_format, and latex_format")
        if core_info[0] != label_class.__name__:
            raise ValueError(
                "Expecting core_info[0] to be '%s'"%label_class.__name__)
        if fence_when_forced:
            made_label = label_class(core_info[1], core_info[2],
                                     fence_when_forced=True,
                                     styles=styles)
        else:
            made_label = label_class(core_info[1], core_info[2], 
                                     styles=styles)
        return made_label

    def remake_arguments(self):
        '''
        Yield the argument values that could be used to recreate the
        Label.  This is a default for simple Labels, Variables, or Literals.
        '''
        from .literal import Literal
        sig = signature(self.__class__.__init__)
        init_params = sig.parameters
        if len(init_params) == 1:
            return  # no arguments (except self) are taken
        is_literal_instance = isinstance(self, Literal)
        known_param_names = {'self', 'string_format', 'latex_format', 
                             'fence_when_forced', 'extra_core_info',
                             'styles'}
        if self.__class__ == Label:
            known_param_names.add('label_type')
        if is_literal_instance:
            known_param_names.add('theory')
        unknown_param_names = init_params.keys() - known_param_names
        if len(unknown_param_names) > 0:
            raise LabelError(
                "Must properly implement the 'remake_arguments' method for class %s "
                "given unkown parameter names, %s"
                %(self.__class__, ', '.join(unknown_param_names)))
        core_info = self.core_info()
        string_format, latex_format = core_info[1:3]
        yield '"' + string_format + '"'
        if 'latex_format' in init_params and latex_format != string_format:
            yield ('latex_format', 'r"' + latex_format + '"')
        if self.fence_when_forced:
            assert core_info[3] == 'fence_when_forced'
            extra_core_info = core_info[4:]
        else:
            extra_core_info = core_info[3:]
        if 'fence_when_forced' in init_params and self.fence_when_forced:
            yield ('fence_when_forced', True)
        if is_literal_instance:
            theory_name = extra_core_info[0]
            extra_core_info = extra_core_info[1:]
            if 'theory' in init_params:
                yield ('theory', '"' + theory_name + '"')
        if 'extra_core_info' in init_params and len(extra_core_info) > 0:
            yield ('extra_core_info', extra_core_info)

class LabelError(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg
