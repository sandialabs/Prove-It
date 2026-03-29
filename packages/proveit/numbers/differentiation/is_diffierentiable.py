from proveit import Operation, Literal, Lambda, U, f, g, prover, x, free_vars, c, n
from proveit.numbers import Exp, Add, Real, Mult, Numeral, sqrt, frac, one, two, Neg, zero, greater, Rational, Natural, IntegerNeg, readily_provable_number_set

class IsDifferentiable(Operation):
    '''
    IsDifferentiable(f, U) means f is differentiable over domain U.
    '''

    _operator_ = Literal(
        'IsDifferentiable',
        r'\textrm{IsDifferentiable}',
        theory=__file__
    )

    def __init__(self, func, U, *, styles=None):
        Operation.__init__(self, IsDifferentiable._operator_, (func, U),
                           styles=styles)
        self.func = func
        self.U = U

    def latex(self, **kwargs):
        func_str = self.func.latex(fence=True)
        U_str = self.U.latex(fence=True)
        return r'{\rm IsDifferentiable}(' + func_str + r', ' + U_str + r')'

    def string(self, **kwargs):
        func_str = self.func.string(fence=True)
        U_str = self.U.string(fence=True)
        return 'IsDifferentiable(' + func_str + ', ' + U_str + ')'

    @prover
    def conclude(self,**defaults_config):

        if isinstance(self.func, Lambda):

            if self.func.body == self.func.parameter:
                from proveit.numbers.differentiation import x_isDiff
                return x_isDiff.instantiate({U:self.U, x:self.func.parameter})
            
            if self.func.parameter not in free_vars(self.func.body):
                from proveit.numbers.differentiation import const_isDiff
                return const_isDiff.instantiate({U:self.U, x:self.func.parameter, c:self.func.body})

            if isinstance(self.func.body,Add):
                from proveit.numbers.differentiation import add_isDiff
                _f = Lambda(self.func.parameter, self.func.body.operands[0])
                _g = Lambda(self.func.parameter, self.func.body.operands[1])
                return add_isDiff.instantiate({U:self.U, f:_f, g:_g})
               
            if isinstance(self.func.body,Mult):
                from proveit.numbers.differentiation import prod_isDiff
                _f = Lambda(self.func.parameter, self.func.body.operands[0])
                _g = Lambda(self.func.parameter, self.func.body.operands[1])
                return prod_isDiff.instantiate({U:self.U, f:_f, g:_g})
            
            if isinstance(self.func.body,Neg):
                from proveit.numbers.differentiation import Neg_isDiff
                _f = Lambda(self.func.parameter, self.func.body.operands[0])
                return Neg_isDiff.instantiate({U:self.U, f:_f})
            
            if isinstance(self.func.body,Exp):
                print("expo is differentiable")
                # from proveit.numbers.differentiation import exp_isDiff
            
                _f = Lambda(self.func.parameter, self.func.body.base)
                _n = self.func.body.exponent
                _nset = readily_provable_number_set(_n, default=Real)

                if _n == frac(one,two):
                    from proveit.numbers.differentiation import sqrt_isDiff
                    return sqrt_isDiff.instantiate({U:self.U, f:_f, n:_n })
                
                if Natural.readily_includes(_nset):
                    from proveit.numbers.differentiation import exp_pos_isDiff
                    return exp_pos_isDiff.instantiate({U:self.U, f:_f, n:_n })
                
                if IntegerNeg.readily_includes(_nset):
                    from proveit.numbers.differentiation import exp_neg_isDiff
                    return exp_neg_isDiff.instantiate({U:self.U, f:_f, n:_n })

                # exit with an error      
                
                # return exp_isDiff.instantiate({U:self.U, f:_f, n:_n })
            
            