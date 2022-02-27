from proveit import Function, Literal

class Log(Function):
    # operator of the Log operation.
    _operator_ = Literal(string_format='log', latex_format=r'\textrm{log}',
                         theory=__file__)    
    
    def __init__(self, base, antilog, *, styles=None):
        Function.__init__(self, Log._operator_, (base, antilog),
                          styles=styles)
        self.base = base
        self.antilog = antilog

    def string(self, **kwargs):
        return Log._operator_.string() + "_%s(%s)"%(
                self.base.string(), self.antilog.string())

    def latex(self, **kwargs):
        return Log._operator_.latex() + r"_%s\left(%s\right)"%(
                self.base.latex(), self.antilog.latex())