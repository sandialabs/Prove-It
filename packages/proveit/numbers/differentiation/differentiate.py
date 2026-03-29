from proveit import prover, Lambda, n, x, y, U, f, g, c, Composition, free_vars, Function
from proveit.decorators import equality_prover
from proveit._core_.expression.operation import Operation
from proveit._core_.expression.label.literal import Literal
from proveit.numbers import Exp, Add, Real, Mult, Numeral, sqrt, frac, one, two, Neg, readily_provable_number_set
from proveit.logic import Equals


class Differentiate(Operation):
    '''
    A Differentiate is an Expression that represents the differentiation
    of functions (lambda maps).
    '''
    
    # operator of the Add operation
    _operator_ = Literal(string_format='D', latex_format=r'D', 
                         theory=__file__)
    
    def __init__(self, *maps, styles=None):
        Operation.__init__(self, Differentiate._operator_, maps, 
                           styles=styles)

    @prover
    def application_simplification(self, operands, *, must_evaluate=False,
                                   **defaults_config):
        operand=operands[0]
        func = self.operands[0]
        _U = readily_provable_number_set(operand, default=Real)
        print("operand",operand)
        print("func",func)
        # IMPLEMENT operand-specific SIMPLIFICATIONS BELOW
      
       
        if isinstance(func,Lambda):
            diff = None

            if func.parameter not in free_vars(func.body):
                print("free vars const!")
                from proveit.numbers.differentiation import diff_const
                diff = diff_const.instantiate({x:func.parameter, c: func.body, y: operand})
                print(diff)
                return diff
            
            if func.body == func.parameter:
                from proveit.numbers.differentiation import diff_x
                diff = diff_x.instantiate({x:func.parameter, y: operand})
                return diff
            
            if func.body.operator == sqrt:
                if func.parameter == func.body.base :
                    from proveit.numbers.differentiation import diff_exponent
                    print("sqrt!")
                    diff = diff_exponent.instantiate({n:frac(one,two),x:func.parameter,y:operand})
                    return diff

            if isinstance(func.body,Exp):
                print("exp!")
                print("func para",func.parameter,"func body base",func.body.base)
                if func.parameter == func.body.base :
                    print("inside if1")
                    from proveit.numbers.differentiation import diff_exponent
                
                    diff = diff_exponent.instantiate({n:func.body.exponent,x:func.parameter,y:operand})
                    print(diff)
                    return diff
                
                # # # works fine 
                # elif func.parameter not in free_vars(func.body.exponent):
                #     # x ↦ f(x)^c : (x ↦ x^c) ∘ (x ↦ f(x))
                #     composition = Composition(Lambda(func.parameter, Exp(func.parameter,func.body.exponent)),
                #                                Lambda(func.parameter,func.body.base))
                #     # (x ↦ x^c) ∘ (x ↦ f(x)) = x -> f(x)^c
                #     comp_eq = composition.shallow_simplification()
                #     # D [(x ↦ x^c) ∘ (x ↦ f(x))](y) = D[x^c](f(x)).D[f(x)](y)
                #     comp_diff = Differentiate(composition)
                #     print("comp_diff",comp_diff)
                #     return comp_diff.application_simplification(operands)
                    

                elif func.parameter not in free_vars(func.body.exponent):
                    print("inside if2")
                    # x ↦ f(x)^c : (x ↦ x^c) ∘ (x ↦ f(x))
                    from proveit.numbers.differentiation import diff_chainrule
                    _f = Lambda(func.parameter, Exp(func.parameter,func.body.exponent))
                    _g = Lambda(func.parameter,func.body.base)
                    return diff_chainrule.instantiate({U:_U, f:_f, g:_g, y:operand})

                    composition = Composition(Lambda(func.parameter, Exp(func.parameter,func.body.exponent)),
                                                Lambda(func.parameter,func.body.base))
                    # (x ↦ x^c) ∘ (x ↦ f(x)) = x -> f(x)^c
                    comp_eq = composition.shallow_simplification()
                    # D [(x ↦ x^c) ∘ (x ↦ f(x))](y) = D[x^c](f(x)).D[f(x)](y)
                    comp_diff = Differentiate(composition)
                  
                    comp_diff_eq = comp_diff.application_simplification(operands, preserve_expr=Function(comp_diff, operand))
                    # D[x-> f(x)^c](y) = D[x^c](f(x)).D[f(x)](y)
                    # print("comp_eq:",comp_eq)
                    # print("comp_diff_eq:",comp_diff_eq)
                    # print("comp_diff_lhs_op",comp_diff_eq.inner_expr().lhs.operator.operand)
                    return comp_diff_eq.inner_expr().lhs.operator.operand.substitute(comp_eq)

            if isinstance(func.body,Add):
                if func.body.operands.is_double():
                    print("in Add")
                    from proveit.numbers.differentiation import diff_add
                    _f = Lambda(func.parameter, func.body.operands[0])
                    _g = Lambda(func.parameter, func.body.operands[1])
                
                    diff = diff_add.instantiate({U:_U,f:_f,g:_g,x:func.parameter,y:operand})
                    return diff 
                
            if isinstance(func.body, Neg):
                print("in neg")
                from proveit.numbers.differentiation import diff_neg
                _f = Lambda(func.parameter, func.body.operands[0])
                diff = diff_neg.instantiate({U:_U,f:_f,x:func.parameter,y:operand})
                return diff 

                
            if isinstance(func.body,Mult):
                if func.body.operands.is_double():
                    print("in mult")
                    from proveit.numbers.differentiation import diff_prod
                    _f = Lambda(func.parameter, func.body.operands[0])
                    _g = Lambda(func.parameter, func.body.operands[1])
                
                    diff = diff_prod.instantiate({U:_U,f:_f,g:_g,x:func.parameter,y:operand})
                    return diff 
              
        if isinstance(func, Composition):
            print("composition")
            from proveit.numbers.differentiation import diff_chainrule
            _f = func.operands[0]
            _g = func.operands[1]
            print("_f, _g", _f, _g)
            diff = diff_chainrule.instantiate({U:_U, f:_f, g:_g, y:operand})
            print("diff", diff)
            return diff
   
        return Equals(Function(self, operands),Function(self, operands)).prove()





            