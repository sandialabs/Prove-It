from proveit import Function, Literal,equality_prover

class Adj(Function):

    _operator_ = Literal(string_format='Adj', theory=__file__)

    def __init__(self, lin_op, *, styles=None):
        '''
        Denote the Hermitan adjoint of a linear operator.
        '''
        Function.__init__(self, Adj._operator_, lin_op,
                          styles=styles)

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions
        options = StyleOptions(self)
        options.add_option(
            name = 'notation',
            description = ("Could be 'normal' or 'Dirac' (for quantum notation)"),
            default = 'normal', 
            related_methods = ('with_notation'))
        return options

    def with_notation(self, notation):
        return self.with_styles(notation=notation)


    def latex(self, **kwargs):
        _a = self.operand
        def _is_ket_variable(expr):
            from proveit._core_.expression.label.var import Variable
            if not isinstance(expr, Variable):
                return False
            latex = expr.latex()
            return latex.startswith(r'\lvert') and latex.endswith(r'\rangle')
        
        def _strip_ket_delimiters(latex):
            return latex.replace(r'\lvert', '').replace(r'\rangle', '').strip()


        notation = self.get_style('notation', 'normal')

        if (notation == 'dirac') and (_is_ket_variable(_a)):

            inner = _strip_ket_delimiters(_a.latex())

            return r'\langle %s \rvert' % (inner)

        return self.operand.string(fence=True) + r'^{\dagger}'
    
    ##### newly added
    @equality_prover('distributed', 'distribute')
    def distribution(self,**defaults_config):
        if hasattr(self.operand, 'adjoint_distribution'):
            return self.operand.adjoint_distribution()


    def string(self, **kwargs):
        _a = self.operand
        def _is_ket_variable(expr):
            from proveit._core_.expression.label.var import Variable
            if not isinstance(expr, Variable):
                return False
            latex = expr.latex()
            return latex.startswith(r'\lvert') and latex.endswith(r'\rangle')
        
        def _strip_ket_delimiters(latex):
            return latex.replace(r'\lvert', '').replace(r'\rangle', '').strip()

        if _is_ket_variable(_a):

            inner = _strip_ket_delimiters(_a.latex())

            return '<%s|' % (inner)

        return self.operand.string(fence=True) + '*'

    # def string(self, **kwargs):
    #     # replace with unicode dagger when unicode formats are
    #     # implemented
    #     return self.operand.string(fence=True) + '*'

    # def latex(self, **kwargs):
    #     return self.operand.string(fence=True) + r'^{\dagger}'
