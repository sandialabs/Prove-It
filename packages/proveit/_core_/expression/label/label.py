from proveit._core_.expression.expr import Expression
from proveit._core_.expression.style_options import StyleOptions
from proveit._core_.expression.fencing import (
        maybe_fenced_string, maybe_fenced_latex)
import re

class Label(Expression):
    """
    Label is the base class for the Variable, Literal, and Multi_variable expr
    classes (Label is not itself an expr class).  It is a mathematical label
    with string and latex formatting.
    """
    def __init__(self, string_format, latex_format=None, label_type = 'Label', 
                 extra_core_info = tuple(), sub_expressions=tuple(),
                 fence_when_forced=False, styles=None):
        '''
        Create a Label with the given string and latex formatting.
        By default, the latex formatting is the same as the string formatting.
        '''
        self.string_format = string_format
        if latex_format is None: latex_format = string_format
        self.latex_format = latex_format.strip() if latex_format is not None else string_format
        assert re.match('[!-~]+', self.string_format), 'Label string_format may include only printable ascii characters and no space'
        assert re.match('[ -~]+', self.latex_format), 'Label latex_format may include only printable ascii characters'
        if not isinstance(self.string_format, str):
            raise TypeError("'string_format' must be a str")
        if not isinstance(self.latex_format, str):
            raise TypeError("'latex_format' must be a str")
        if ',' in self.string_format or ',' in self.latex_format:
            raise ValueError("Comma not allowed within a label's formatting")
        if styles is None:
            styles = dict()
        if fence_when_forced: 
            styles['fence'] = 'when forced'
        core_info = [label_type] + self._labelInfo() + list(extra_core_info)
        Expression.__init__(self, core_info, sub_expressions=sub_expressions,
                            styles=styles)

    def style_options(self):
        options = StyleOptions(self)
        options.add('fence', "Do we need to wrap in paranthesis: 'when forced' or 'never'?")
        return options
        
    def string(self, **kwargs):
        '''
        Return a string representation of the Label.
        '''
        if self.get_style('fence', 'never')=='when forced':
            kwargs['fence'] = (kwargs['force_fence'] if 'force_fence' in 
                               kwargs else False)
            return maybe_fenced_string(self.string_format, **kwargs)
        return self.string_format

    def latex(self, **kwargs):
        '''
        Return a latex representation of the Label.
        '''
        if self.get_style('fence', 'never')=='when forced':
            kwargs['fence'] = (kwargs['force_fence'] if 'force_fence' in 
                               kwargs else False)
            return maybe_fenced_latex(self.latex_format, **kwargs)
        return self.latex_format

    def _labelInfo(self):
        '''
        Return the Label's info to be used in the expr's core info.
        '''
        return [self.string_format, self.latex_format]    
    
    @classmethod
    def _make(label_class, core_info, styles, sub_expressions):
        if len(sub_expressions) > 0:
            raise ValueError('Not expecting any sub_expressions of Label')
        if len(core_info) != 3:
            raise ValueError("Expecting " + label_class.__name__ + " core_info to contain 3 items: '" + label_class.__name + "', string_format, and latex_format")
        if core_info[0] != label_class.__name__:
            raise ValueError("Expecting core_info[0] to be '" + label_class.__name__ + "'")
        return label_class(core_info[1], core_info[2]).with_styles(**styles)

    def remake_arguments(self):
        '''
        Yield the argument values that could be used to recreate the 
        Label.  This is a default for simple Labels, Variables, or Literals.
        '''
        import inspect
        init_args = inspect.getargspec(self.__class__.__init__)[0]
        if len(init_args)==1:
            return # no arguments (except self) are taken
        if len(init_args)>=3 and init_args[1]=='string_format' and init_args[2]=='latex_format':
            string_format, latex_format = self.core_info()[1:3]
            yield '"' + string_format + '"'
            if latex_format != string_format:
                yield ('latex_format', 'r"' + latex_format + '"')
        else:
            raise LabelError("Must properly implement the 'remake_arguments' method for class %s"%str(self.__class__))
        if 'styles' in init_args and len(self.get_styles()) > 0:
            yield ('styles', self.get_styles())
        if 'fence_when_forced' in init_args and self.get_style('fence', 'never')=='when forced':
            yield ('fence_when_forced', True)

class LabelError(Exception):
    def __init__(self, msg):
        self.msg = msg
    
    def __str__(self):
        return self.msg
