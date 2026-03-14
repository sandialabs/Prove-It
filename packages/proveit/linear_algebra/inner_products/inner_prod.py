from proveit import (Operation, Literal, UnsatisfiedPrerequisites,
                     equality_prover)
from proveit import a, b, x, y, z, u, H, K
from proveit.logic import is_irreducible_value, Equals
from proveit.numbers import one 


class InnerProd(Operation):
    _operator_ = Literal(
            string_format=r'InnerProd', latex_format=r'\textrm{InnerProd}',
            theory=__file__)
    
    def __init__(self, a, b, *, styles=None):
        Operation.__init__(self, InnerProd._operator_,
                           (a, b), styles=styles)

    def style_options(self):
        options = super().style_options()
        options.add_option(
            name='notation',
            description="Inner product notation: 'standard' or 'dirac'",
            default='standard',
            related_methods=()
        )
        return options

    

    def with_notation(self, notation):
        return self.with_styles(notation=notation)

    def latex(self, **kwargs):

        def _is_ket_variable(expr):
            from proveit._core_.expression.label.var import Variable
            if not isinstance(expr, Variable):
                return False
            latex = expr.latex()
            return latex.startswith(r'\lvert') and latex.endswith(r'\rangle')
        
        def _strip_ket_delimiters(latex):
            return latex.replace(r'\lvert', '').replace(r'\rangle', '').strip()


        notation = self.get_style('notation', 'standard')

        _a, _b = self.operands.entries

        if (notation == 'dirac' and
            _is_ket_variable(_a) and
            _is_ket_variable(_b)):

            left_inner = _strip_ket_delimiters(_a.latex())
            right_inner = _strip_ket_delimiters(_b.latex())

            return r'\langle %s \mid %s \rangle' % (left_inner, right_inner)

        return (r'\left \langle ' + _a.latex() + ', ' 
                + _b.latex() + r'\right \rangle')
    
    def string(self, **kwargs):
        _a, _b = self.operands.entries
        def _is_ket_variable(expr):
            from proveit._core_.expression.label.var import Variable
            if not isinstance(expr, Variable):
                return False
            latex = expr.latex()
            return latex.startswith(r'\lvert') and latex.endswith(r'\rangle')
        
        def _strip_ket_delimiters(latex):
            return latex.replace(r'\lvert', '').replace(r'\rangle', '').strip()

        if (_is_ket_variable(_a) and _is_ket_variable(_b)):

            left_inner = _strip_ket_delimiters(_a.latex())
            right_inner = _strip_ket_delimiters(_b.latex())

            return '<%s|%s>' % (left_inner, right_inner)

        return '<' + _a.string() + ', ' + _b.string() + '>'
    
    # def string(self, **kwargs):
    #     _a, _b = self.operands
    #     return '<' + _a.string() + ', ' + _b.string() + '>'
    
    # def latex(self, **kwargs):
    #     _a, _b = self.operands
    #     return (r'\left \langle ' + _a.latex() + ', ' 
    #             + _b.latex() + r'\right \rangle')

    
    
    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Simplify via inner product linearity:
        <a x, y> = a <x, y>
        <x, y> = <x, a y>
        <x + y, z> = <x, z> + <y, z>
        <x, y + z> = <x, y> + <x, z>
        '''

        from proveit.linear_algebra import VecSpaces, ScalarMult, VecAdd, Hspace, VecNeg
        from proveit.linear_algebra.inner_products import (
        inner_prod_scalar_mult_left, inner_prod_scalar_mult_right,
        inner_prod_vec_add_left, inner_prod_vec_add_right, Norm, inner_prod_in_field, innerprod_normality, inner_prod_vec_neg_left, inner_prod_vec_neg_right)
        from proveit.physics.quantum import var_ket_psi

        _u, _v = self.operands
        try:
            vec_space = VecSpaces.common_known_vec_space((_u, _v))
        except UnsatisfiedPrerequisites:
            # No known common vectors space for the operands, so
            # we have no specific shallow_simplication we can do here.
            return Operation.shallow_simplification(
                    self, must_evaluate=must_evaluate)
        field = VecSpaces.known_field(vec_space) #additional line Wayne suggested
        inner_prod_in_field.instantiate({K:field, H:vec_space, x:_u, y:_v})
        simp = None
        if isinstance(_u, ScalarMult):
            simp = inner_prod_scalar_mult_left.instantiate(
                    {K:field, H:vec_space, a:_u.scalar, x:_u.scaled, y:_v})
        if isinstance(_v, ScalarMult):
            simp = inner_prod_scalar_mult_right.instantiate(
                    {K:field, H:vec_space, a:_v.scalar, x:_u, y:_v.scaled})
        if isinstance(_u, VecAdd):
            simp = inner_prod_vec_add_left.instantiate(
                    {K:field, H:vec_space, x:_u.terms[0], y:_u.terms[1], z:_v})
        if isinstance(_v, VecAdd):
            simp = inner_prod_vec_add_right.instantiate(
                    {K:field, H:vec_space, x:_u, y:_v.terms[0], z:_v.terms[1]})

        # our if statements
        if _u==_v and Equals(Norm(_u), one).proven():
          simp = innerprod_normality.instantiate({Hspace:vec_space, var_ket_psi:_u})   

        if isinstance(_u, VecNeg):
            simp= inner_prod_vec_neg_left.instantiate({K:field, H:vec_space, x:_u.operand, y:_v})

        if isinstance(_v, VecNeg):
            simp= inner_prod_vec_neg_right.instantiate({K:field, H:vec_space, x:_u, y:_v.operand})

        if simp is None:
            return Operation.shallow_simplification(
                    self, must_evaluate=must_evaluate)
        if must_evaluate and not is_irreducible_value(simp.rhs):
            return simp.inner_expr().rhs.evaluate()
            
        return simp

