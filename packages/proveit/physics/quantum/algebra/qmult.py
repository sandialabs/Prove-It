from proveit import (Operation, Literal, Lambda, ExprTuple, ExprRange,
                     UnsatisfiedPrerequisites, SimplificationDirectives,
                     prover, equality_prover, relation_prover)
from proveit import (a, b, c, f, i, j, l, m, n, A, B, C, M, Q, U, X, Y,
                     alpha)
from proveit.relation import TransRelUpdater
from proveit.logic import Equals, InSet, ClassMembership, InClass, CartExp
from proveit.numbers import Complex, subtract, one, two, Exp
from proveit.abstract_algebra.generic_methods import (
        apply_association_thm, apply_disassociation_thm)
from proveit.linear_algebra import (VecSpaces, VecAdd, VecSum, LinMap,
                                    MatrixSpace, Norm, 
                                    HilbertSpaces, Hspace)

class Qmult(Operation):
    '''
    A Qmult Operation can string together a sequences of quantum 
    operators and/or kets.  Properly defined, a ket is a vector
    in a Hilbert space and a quantum operator acts (under Qmult)
    as a linear map from a Hilbert space to either the same Hilbert 
    space or a complex number.  The latter is denoted as a 'bra'.
    Using 'op' to denote a quantum operator from Hilbert space to
    Hilbert space, the following combinations are defined:
        Qmult(bra, ket) : c-number
        Qmult(op, ket)  : ket
        Qmult(bra, op)  : bra
        Qmult(op, op)   : op
        Qmult(ket, bra) : op
        Qmult(X, c-number) : X
        Qmult(c-number, X) : X
    where X is a ket, bra, op, or c-number.
    
    Qmult(ket, ket), Qmult(bra, bra),
    Qmult(ket, op), Qmult(op, bra) are NOT defined.
    
    When a Qmult is applied to a single quantum operator, it 
    denotes the mapping represented by the operand:
        Qmult(op) : ket -> ket
        Qmult(bra) : ket -> c-number
        
    The formatting is the same as for matrix multiplication with
    just thin spaces in LaTeX except when there is a single
    operand in which case we wrap the operand in square brackets
    to denote that it represents the corresponding mapping.
    '''
    
    _operator_ = Literal(string_format=r'.', latex_format=r'\thinspace',
                         theory=__file__)

    _simplification_directives_ = SimplificationDirectives(
            ungroup = True, factor_scalars=True, use_scalar_mult=True)

    def __init__(self, *operands, styles=None):
        Operation.__init__(self, Qmult._operator_, operands,
                           styles=styles)
    
    def string(self, **kwargs):    
        if self.operands.is_single():
            # Single operand: wrap it in square braces to show
            # we are treating it as an operator (a function).
            return '[' + self.operand.string() + ']'
        return Operation.string(self, **kwargs)
        
    def latex(self, **kwargs):    
        # Turn sub-fence on since the operator is just a space that
        # doesn't serve as a good delimiter of the operands.
        if self.operands.is_single():
            # Single operand: wrap it in square braces to show
            # we are treating it as an operator (a function).
            return r'\left[' + self.operand.latex() + r'\right]'
        kwargs['sub_fence'] = True
        return Operation.latex(self, **kwargs)

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Qmult
        expression assuming the operands have been simplified.
        
        Currently deals only with:
        (1) simplify unary case
        (2) Ungrouping nested tensor products.
        (3) Factoring out scalars.
        '''
        from proveit.linear_algebra import ScalarMult
        from proveit.physics.quantum import (
                Bra, Ket, HilbertSpaces,
                varphi, var_ket_psi)
        yield_known_hilbert_spaces = HilbertSpaces.yield_known_hilbert_spaces
        
        if self.operands.is_single():
            # Handle unary cases
            from . import (qmult_of_ket, qmult_of_bra, qmult_of_complex,
                           qmult_of_linmap)
            operand = self.operands[0]
            if InSet(operand, Complex).proven():
                # Qmult of a complex number is just the complex number
                return qmult_of_complex.instantiate({c:operand})
            elif isinstance(operand, Bra):
                # Qmult of a bra is the bra (equal to the 
                # linear map it represents).
                for _Hspace in yield_known_hilbert_spaces(
                        Ket(operand.operand)):
                    return qmult_of_bra.instantiate(
                            {Hspace:_Hspace, varphi:operand.operand})
            elif InClass.has_known_membership(
                    operand, domain_type=MatrixSpace._operator_):
                # Qmult of a matrix.  It equates to a lambda
                # map, but this isn't considered a simplification.
                # Use linmap_reduction instead if this is desired.
                return Equals(self, self).conclude_via_reflexivity()
            else:
                for _Hspace in yield_known_hilbert_spaces(operand):
                    # Qmult of a ket is just the ket
                    return qmult_of_ket.instantiate(
                            {Hspace:_Hspace, var_ket_psi:operand})
                for linmap in containing_hilbert_space_linmap_sets(operand):
                    # Qmult of a linear map is just the linear map
                    _Hspace, _X = linmap.from_vspace, linmap.to_vspace
                    return qmult_of_linmap.instantiate(
                            {Hspace:_Hspace, X:_X, A:operand})
                return Equals(self, self).conclude_via_reflexivity()

        # for convenience updating our equation:
        expr = self
        eq = TransRelUpdater(expr)
        
        if Qmult._simplification_directives_.ungroup:
            # ungroup the expression (disassociate nested additions).
            _n = 0
            length = expr.operands.num_entries() - 1
            # loop through all operands
            while _n < length:
                operand = expr.operands[_n]
                # print("n, length", n, length)
                if isinstance(operand, Qmult):
                    # if it is grouped, ungroup it
                    expr = eq.update(expr.disassociation(
                            _n, preserve_all=True))
                elif isinstance(operand, ScalarMult):
                    # ungroup contained ScalarMult's
                    expr = eq.update(expr.scalar_mult_absorption(
                            _n, preserve_all=True))                    
                length = expr.operands.num_entries()
                _n += 1
        
        if Qmult._simplification_directives_.factor_scalars:
            # Next, pull out scalar factors
            expr = eq.update(expr.factorization_of_scalars())
        
        if Qmult._simplification_directives_.use_scalar_mult:
            # Finally, use ScalarMult for any scalar operands.
            if (isinstance(expr, Qmult) and 
                    expr.operands.num_entries() > 1 and 
                    InSet(expr.operands[0], Complex).proven()):
                expr = eq.update(expr.scalar_mult_factorization())
        if must_evaluate==True:
            if isinstance(expr,ScalarMult):
                try:
                    expr = eq.update(expr.inner_expr().scaled.projection())
                    expr = eq.update(expr.evaluation())
                except ValueError:
                    pass
            else:
                try:
                    expr = eq.update(expr.projection())
                    expr = eq.update(expr.evaluation())
                except ValueError:
                    pass
                
            #expr = eq.update(expr.evaluation())        
        return eq.relation
    #
    @equality_prover('adjoint_distributed', 'adjoint_distribute')
    def adjoint_distribution(self,**defaults_config):
        if self.operands.is_double():
            _A = self.operands[0]
            _B = self.operands[1]
            for linmap in containing_hilbert_space_linmap_sets(_B):
                _Hspace, _X = linmap.from_vspace, linmap.to_vspace
                for linmap in containing_hilbert_space_linmap_sets(_A):
                    _Y = linmap.to_vspace
                    return adjoint_binary_distribution.instantiate({Hspace:_Hspace,X:_X,Y:_Y,A:_A,B:_B})
        else:
            raise NotImplementedError("We only treat adjoint distribution when there are two operands")
        
    @equality_prover('projected', 'project')
    def projection(self,**defaults_config):
        from . import qmult_op_ket, ket_self_projection
        from proveit.physics.quantum import (
                Bra, Ket, HilbertSpaces, var_ket_psi,psi)
        from proveit.logic import Equals
        if not self.operands.is_double():
            raise ValueError("'projection' method only works when there are two operands")
        M,ket = self.operands
        #try:
        linmap_eq = Qmult(M).linmap_reduction()
       # except ValueError:
        #    pass
        yield_known_hilbert_spaces = HilbertSpaces.yield_known_hilbert_spaces
        for _Hspace in yield_known_hilbert_spaces(ket):
            if isinstance(M, Bra) and M.operand==ket.operand and ket_self_projection.is_usable():
            #if M.operand==ket.operand:
                #print("same")
                self_proj_eq=ket_self_projection.instantiate({Hspace: _Hspace, psi:ket.operand})
                #print(self_proj_eq)
                #return linmap_eq.sub_right_side_into(self_proj_eq.inner_expr().rhs.operator)
                return self_proj_eq
            #bra_eq=bra_def.instantiate({varphi:bra.operand, Hspace: _Hspace})
            #return bra_eq.sub_right_side_into(qmult_eq.inner_expr().rhs.operator)
            else:
                #print("different")
                qmult_eq=qmult_op_ket.instantiate({A:M, Hspace: _Hspace, X: Complex, var_ket_psi: ket})
                #print(qmult_eq)
                return linmap_eq.sub_right_side_into(qmult_eq.inner_expr().rhs.operator)

    @equality_prover('linmap_reduced', 'linmap_reduce')
    def linmap_reduction(self, **defaults_config):
        '''
        Equate the Qmult to a linear map, if possible.
        '''
        from proveit.physics.quantum import QmultCodomain
        # In the process of proving that 'self' is in QmultCodomain,
        # it will prove it is a linear map if it can.
        QmultCodomain.membership_object(self).conclude()
        from proveit.physics.quantum import (
                Bra, Ket, HilbertSpaces, varphi)
        #from proveit.physics.quantum.algebra import Hspace
        from . import qmult_of_matrix, qmult_of_bra_as_map

        yield_known_hilbert_spaces = HilbertSpaces.yield_known_hilbert_spaces
        if self.operands.is_single():
            # Unary Qmult
            operand = self.operand
            for mspace_membership in InClass.yield_known_memberships(
                    operand, domain_type=MatrixSpace._operator_):
                # Qmult of a matrix is the linear map
                # represented by the matrix.
                mspace = mspace_membership.domain
                _m, _n = (mspace.operands['rows'], 
                          mspace.operands['columns'])
                return qmult_of_matrix.instantiate(
                    {m:_m, n:_n, M:operand})
            if isinstance(operand, Bra):
                for _Hspace in yield_known_hilbert_spaces(
                        Ket(operand.operand)):
                    return qmult_of_bra_as_map.instantiate(
                            {Hspace:_Hspace, varphi:operand.operand})
        else:
            raise NotImplementedError(
                    "'linmap_reduction' currently only impoemented "
                    "for a unary Qmult")
        raise ValueError("%s does not evaluate to a linear map"%self)

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field,
                            **defaults_config):
        '''
        Prove that this Qmult is in a vector space (e.g., if it is
        a ket).
        '''
        from proveit.physics.quantum import QmultCodomain
        # In the process of proving that 'self' is in QmultCodomain,
        # it will prove it is a vector in a Hilbert space if
        # appropriate.
        QmultCodomain.membership_object(self).conclude()
        if vec_space is not None:
            return InSet(self, vec_space).prove()
        return InSet(self, 
                     VecSpaces.known_vec_space(self, field=field)).prove()

    @equality_prover('associated', 'associate')
    def association(self, start_idx, length, **defaults_config):
        '''
        Given a valid Qmult operation (valid sequence of bras, kets,
        and/or quantum operations), deduce that this expression is equal 
        to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (A B ... Y Z) = (A B ... (L ... M) ... Y Z).
        '''
        from . import qmult_association
        eq = apply_association_thm(
            self, start_idx, length, qmult_association)
        return eq.with_wrapping_at()

    @equality_prover('disassociated', 'disassociate')
    def disassociation(self, idx, **defaults_config):
        '''
        Given a valid Qmult operation (valid sequence of bras, kets,
        and/or quantum operations), deduce that this expression is equal 
        to a form in which the operand
        at index idx is no longer grouped together.
        For example, (A B ... (L ... M) ... Y Z) = (A B ... Y Z).
        '''
        from . import qmult_disassociation
        eq = apply_disassociation_thm(
                self, idx, qmult_disassociation)
        return eq.with_wrapping_at()

    @equality_prover('scalar_mult_absorbed', 'scalar_mult_absorb')
    def scalar_mult_absorption(self, idx, **defaults_config):
        '''
        Given a valid Qmult operation (valid sequence of bras, kets,
        and/or quantum operations), equate it to a form in which
        a ScalarMult operand at the given index is absorbed into 
        the Qmult.
        For example, (A B ... (c · M) ... Y Z) = (A B ... c M ... Y Z).
        '''
        from proveit.linear_algebra import ScalarMult
        from . import scalar_mult_absorption
        if not isinstance(self.operands[idx], ScalarMult):
            raise ValueError("The operand of %s at index %d is not "
                             "a ScalarMult"%(self, idx))
        _A = self.operands[:idx]
        _alpha_B = self.operands[idx]
        _B = _alpha_B.scaled
        _C = self.operands[idx+1:]
        _alpha = _alpha_B.scalar
        _l = _A.num_elements()
        _n = _C.num_elements()
        return scalar_mult_absorption.instantiate(
                {l:_l, n:_n, A:_A, alpha:_alpha, B:_B, C:_C})

    @equality_prover('scalars_factored', 'factor_scalars')
    def factorization_of_scalars(self, **defaults_config):
        '''
        Prove equality with a Qmult in which the complex
        numbers are pulled to the front andassociated together via Mult.
        For example,
            (a A b B c C d D e) = ((a*b*c*d*e) A B C D)
        where a, b, c, d, and e are complex numbers, '*' denotes
        number multiplication, and spaces, here, denote the Qmult
        operation.
        
        Also see scalar_mult_factorization.
        '''
        from . import (QmultCodomain, qmult_pulling_scalar_out_front,
                       qmult_pulling_scalars_out_front,
                       qmult_scalar_association)
        expr = self
        eq = TransRelUpdater(expr)
        
        # First, lets prove the Qmult is well-formed and, in the
        # process, ensure to know which operands are Complex.
        if not InClass(self, QmultCodomain).proven():
            QmultCodomain.membership_object(self).conclude()
        
        # Go through the operands in reverse order so the complex
        # factors will be in the original order out front in the end.
        n_complex_entries = 0
        for _k, operand in enumerate(reversed(self.operands.entries)):
            _idx = self.operands.num_entries() - _k - 1 + n_complex_entries
            if InSet(operand, Complex).proven():
                # We have a complex number to pull out in front.
                _A = expr.operands[:_idx]
                _b = operand
                _C = expr.operands[_idx+1:]
                _l = _A.num_elements()
                _n = _C.num_elements()
                expr = eq.update(qmult_pulling_scalar_out_front.instantiate(
                        {l:_l, n:_n, b:_b, A:_A, C:_C}, preserve_all=True))
                n_complex_entries += 1
            elif isinstance(operand, ExprRange):
                if ExprRange(operand.parameter, InSet(operand.body, Complex),
                             operand.true_start_index, operand.true_end_index).proven():
                    # We have a range of complex numbers to pull out in
                    # front.
                    _A = expr.operands[:_idx]
                    _b = ExprTuple(operand)
                    _C = expr.operands[_idx+1:]
                    _j = _b.num_elements()
                    _l = _A.num_elements()
                    _n = _C.num_elements()
                    thm = qmult_pulling_scalars_out_front
                    expr = eq.update(thm.instantiate(
                            {j:_j, l:_l, n:_n, b:_b, A:_A, C:_C},
                            preserve_all=True))
                    n_complex_entries += 1
        
        # Associate the complex numbers, now out in front.
        _b = expr.operands[:n_complex_entries]
        _A = expr.operands[n_complex_entries:]
        _j = _b.num_elements()
        _l = _A.num_elements()
        if (_b.num_entries() > 0 and not _b.is_single() 
                and _A.num_entries() > 0):
            expr = eq.update(qmult_scalar_association.instantiate(
                    {j:_j, l:_l, b:_b, A:_A}, preserve_expr=expr))
            # The multiplication of complex numbers is complex.
            expr.operands[0].deduce_in_number_set(Complex)
        
        return eq.relation
    
    
    @equality_prover('scalar_mult_factorized', 'scalar_mult_factor')
    def scalar_mult_factorization(self, **defaults_config):
        '''
        Given a Qmult with a scalar operand at the beginning,
        equate it with a ScalarMult version.  For example
        
            ((a*b*c*d*e) A B C D) = ((a*b*c*d*e) · (A B C D))
        
        where '·' denotes scalar multiplication and '*' is number
        multplication.
        
        If Qmult.factorization_of_scalars is performed first, it
        will be in the proper form for doing scalar_mult_factorization.
        '''
        from . import scalar_mult_factorization
        
        # Factor the scalar operand (if there is one at the beginning)
        # as a ScalarMult.
        if self.operands.num_entries() > 1:
            _a = self.operands[0]
            _B = self.operands[1:]
            _j = _B.num_elements()
            return scalar_mult_factorization.instantiate(
                    {j:_j, a:_a, B:_B})
        
        raise NotImplementedError(
                "Qmult.scalar_mult_factorization is only implemented "
                "when there are more than one Qmult entries")

    @equality_prover('distributed', 'distribute')
    def distribution(self, idx, *, field=None,
                     **defaults_config):
        '''
        Given a Qmult operand at the (0-based) index location
        'idx' that is a vector sum or summation, prove the distribution 
        over that Qmult factor and return an equality to the original
        Qmult. For example, we could take the Qmult
            qmult = Qmult(A, B+C, D)
        and call qmult.distribution(1) to obtain:
            |- Qmult(A, B+C, D) =
               Qmult(A, B, D) + Qmult(A, C. D)
        '''
        from . import (qmult_distribution_over_add,
                       qmult_distribution_over_summation)
        sum_factor = self.operands[idx]
        _A = self.operands[:idx]
        _C = self.operands[idx+1:]
        _m = _A.num_elements()
        _n = _C.num_elements()
        if isinstance(sum_factor, VecAdd):
            _B = sum_factor.operands
            _i = _B.num_elements()
            impl = qmult_distribution_over_add.instantiate(
                {i:_i, m:_m, n:_n, A:_A, B:_B, C:_C})
            return impl.derive_consequent().with_wrapping_at()
        elif isinstance(sum_factor, VecSum):
            _b = sum_factor.indices
            _j = _b.num_elements()
            _f = Lambda(sum_factor.indices, sum_factor.summand)
            _Q = Lambda(sum_factor.indices, sum_factor.condition)
            impl = qmult_distribution_over_summation.instantiate(
                    {f:_f, Q:_Q, j:_j, m:_m, n:_n, 
                     b:_b, A:_A, C:_C})
            return impl.derive_consequent().with_wrapping_at()
        else:
            raise ValueError(
                "Don't know how to distribute tensor product over " +
                str(sum_factor.__class__) + " factor")
    
    @prover
    def compute_norm(self, **defaults_config):
        '''
        Compute the normalization of this Qmult.
        
        In the current implementation, we simply prove that
        normalization is preserved when applying a unitary.
        '''
        from proveit.physics.quantum import HilbertSpaces, var_ket_psi
        from . import state_space_preservation, normalization_preservation
        if not self.operands.is_double():
            raise NotImplementedError(
                    "Qmult.compute_norm is only implemented "
                    "for binary Qmults, specifically a unitary applied "
                    "to a normalized vector")
        vec = self.operands[1]
        for _H in HilbertSpaces.yield_known_hilbert_spaces(vec):
            if (isinstance(_H, CartExp) and _H.base == Complex):
                _n = _H.exponent
                _alpha = Norm(vec).computed()
                state_space_preservation.instantiate(
                        {n:_n, U:self.operands[0], var_ket_psi:vec})
                return normalization_preservation.instantiate(
                        {n:_n, U:self.operands[0], var_ket_psi:vec,
                         alpha:_alpha})
        raise NotImplementedError(
                "Qmult.compute_norm is only implemented "
                "for binary Qmults, specifically a unitary applied "
                "to a normalized vector in a known Hilbert space that "
                "is the Cartesian exponent of two to a NaturalPos power.")

class QmultCodomainLiteral(Literal):
    '''
    A product (Qmult, specifically) of a sequence of bras, kets, 
    and/or quantum operators, if and only if they are in a valid 
    sequence (well-formed), will yield a vector in a vector space over 
    complex numbers (including the complex numbers themselves), 
    or a linear map between vectors between vectors spaces over complex
    numbers.  We regard this as a proper class called the QmultCodomain.      
    '''
    def __init__(self, *, styles=None):
        Literal.__init__(self, 'Q*', r'\mathcal{Q^*}', styles=styles)

    @property
    def is_proper_class(self):
        '''
        Vector spaces are proper classes. This indicates that
        InClass should be used instead of InSet when this is a domain.
        '''
        return True
    
    def membership_object(self, element):
        return QmultCodomainMembership(element)

class QmultCodomainMembership(ClassMembership):
    '''
    Defines methods that apply to InClass(element, QmultCodomain) 
    objects via InClass.__getattr__ which calls 
    QmultCodomain.membership_object(element)
    to return a QmultCodomainMembership object.
    '''

    def __init__(self, element):
        from . import QmultCodomain
        ClassMembership.__init__(self, element, QmultCodomain)

    def side_effects(self, judgment):
        return # generator yielding nothing
        yield

    @prover
    def conclude(self, **defaults_config):
        '''
        Prove that the 'element' is in the QmultCodomain
        (e.g., that a Qmult is well-formed).
        '''
        from proveit import ProofFailure
        from proveit.numbers import deduce_in_number_set
        from proveit.physics.quantum import (
                Bra, Ket, varphi, var_ket_psi, HilbertSpaces)
        from proveit.physics.quantum.algebra import (
                QmultCodomain)
        from . import (
                qmult_complex_in_QmultCodomain,
                qmult_complex_left_closure, qmult_complex_right_closure,
                qmult_complex_ket_closure, qmult_ket_complex_closure,
                qmult_complex_op_closure, qmult_op_complex_closure,
                complex_in_QmultCodomain, qmult_nested_closure,
                qmult_ket_is_ket, qmult_ket_in_QmultCodomain,
                qmult_op_ket_is_ket, qmult_op_ket_in_QmultCodomain,
                qmult_ket_bra_is_op, qmult_ket_bra_in_QmultCodomain,
                qmult_op_op_is_op, qmult_op_op_in_QmultCodomain,
                qmult_matrix_is_linmap, qmult_matrix_in_QmultCodomain,
                qmult_bra_is_linmap, qmult_bra_in_QmultCodomain,
                qmult_op_is_linmap, qmult_op_in_QmultCodomain,
                ket_in_QmultCodomain, bra_is_linmap, bra_in_QmultCodomain,
                op_in_QmultCodomain, multi_qmult_def
                )
        element = self.element
        yield_known_hilbert_spaces = HilbertSpaces.yield_known_hilbert_spaces
        
        if isinstance(element, Qmult):
            if element.operands.num_entries() == 0:
                raise ValueError("Qmult with no operands is not defined")
                
            elif element.operands.is_single():
                # Unary Qmult closure
                op = element.operand

                # Handle unary Qmult on a bra.
                if isinstance(op, Bra):
                    thm = None
                    _varphi = op.operand
                    #Ket(_varphi).deduce_in_vec_space(field=Complex)
                    for _Hspace in yield_known_hilbert_spaces(Ket(_varphi)):
                        # Prove membership in the target space
                        # while we are at it.
                        qmult_bra_is_linmap.instantiate(
                                {Hspace:_Hspace, varphi:_varphi},
                                preserve_all=True)
                        used_Hspace = _Hspace
                        thm = qmult_bra_in_QmultCodomain
                    if thm is not None:
                        # Just choose any valid Hilbert space (the last
                        # used one will do) for the QmultCodomain 
                        # membership proof.
                        _Hspace = used_Hspace
                        return thm.instantiate(
                                {Hspace:_Hspace, varphi:_varphi})
                    raise NotImplementedError(
                            "Bra, %s, with no known Hilbert space "
                            "membership for the corresponding Ket. "
                            "Cannot prove %s membership in %s"%
                            (op, element, QmultCodomain))

                # Handle unary nested Qmult
                if isinstance(op, Qmult):
                    # Prove memberships of the nested unary Qmult 
                    # to fascilitate the cases below.
                    QmultCodomain.membership_object(op).conclude()
                    for _Hspace in yield_known_hilbert_spaces(op):
                        # Propagate Hspace membership
                        qmult_ket_is_ket.instantiate(
                                {var_ket_psi:op, Hspace:_Hspace},
                                preserve_all=True)
                    for linmap in containing_hilbert_space_linmap_sets(op):                    
                        # Propagate LinMap membership
                        _Hspace = linmap.from_vspace
                        _X = linmap.to_vspace
                        qmult_op_is_linmap.instantiate(
                                {Hspace:_Hspace, X:_X, A:op},
                                preserve_all=True)
                    return qmult_nested_closure.instantiate({A:op})
                
                # Handle unary complex (soft, first attempt).
                if InSet(op, Complex).proven():
                    return qmult_complex_in_QmultCodomain.instantiate({c:op})
                
                for _attempt in (0, 1):               
                    # Handle unary Qmult on a matrix.
                    for mspace_membership in InClass.yield_known_memberships(
                            op, domain_type=MatrixSpace._operator_):
                        mspace = mspace_membership.domain
                        _m, _n = (mspace.operands['rows'], 
                                  mspace.operands['columns'])
                        # Prove linear map membership while we are
                        # at it.
                        qmult_matrix_is_linmap.instantiate(
                            {m:_m, n:_n, M:op}, preserve_all=True)
                        # Choose any valid matrix space (the last 
                        # used ones will do) for the QmultCodomain
                        # membership proof.
                        return qmult_matrix_in_QmultCodomain.instantiate(
                            {m:_m, n:_n, M:op})
    
                    # Handle unary Qmult on a ket.
                    for _Hspace in yield_known_hilbert_spaces(op):
                        return qmult_ket_in_QmultCodomain.instantiate(
                                {Hspace:_Hspace, var_ket_psi:op})
                    
                    # Handle unary Qmult on a linear map.
                    thm = None
                    for linmap in containing_hilbert_space_linmap_sets(op):
                        _Hspace, _X = linmap.operands
                        # Prove membership in the target space
                        # while we are at it.
                        qmult_op_is_linmap.instantiate(
                                {Hspace:_Hspace, X:_X, A:op}, 
                                preserve_all=True)
                        used_linmap = linmap
                        thm = qmult_op_in_QmultCodomain
                    if thm is not None:
                        # Just choose any valid linmap (the last used 
                        # one will do) for the QmultCodomain membership 
                        # proof.
                        _Hspace, _X = used_linmap.operands
                        return thm.instantiate({Hspace:_Hspace, X:_X, A:op})
    
                    if _attempt==0:
                        # If all else fails, try to deduce that the 
                        # operand is in a vector space.  This is useful
                        # for operators as well as kets since matrix
                        # spaces and linear map sets are vector spaces
                        # (though not inner product spaces, so they 
                        # aren't confused with kets fortunately).
                        if hasattr(op, 'deduce_in_vec_space'):
                            op.deduce_in_vec_space(field=Complex)
                        else:
                            break # No need for a second attempt.

                # Second attempt to prove the element is complex.
                try:
                    deduce_in_number_set(op, Complex)
                    # Complex elements are in QmultCodomain
                    return qmult_complex_in_QmultCodomain.instantiate(
                            {c:op})
                except (ProofFailure, NotImplementedError):
                    pass

            elif element.operands.is_double():
                # Binary Qmult closure
                op1, op2 = element.operands
                
                # Prove memberships of unary Qmult on each of the
                # operands to fascilitate the various cases below.
                QmultCodomain.membership_object(Qmult(op1)).conclude()
                QmultCodomain.membership_object(Qmult(op2)).conclude()
                
                # Handle the case where one of the operands is complex.
                thm = None
                if InSet(op1, Complex).proven():
                    _c, _A = op1, op2
                    thm = qmult_complex_left_closure
                    ket_closure_thm = qmult_complex_ket_closure
                    op_closure_thm = qmult_complex_op_closure
                elif InSet(op2, Complex).proven():
                    _A, _c = op1, op2
                    thm = qmult_complex_right_closure
                    ket_closure_thm = qmult_ket_complex_closure
                    op_closure_thm = qmult_op_complex_closure
                if thm is not None:
                    for _Hspace in yield_known_hilbert_spaces(_A):
                        # If the other op is in any vector space over 
                        # Complex numbers (Hilbert spaces) also 
                        # prove closure within the Hilbert space.
                        ket_closure_thm.instantiate(
                                {c:_c, Hspace:_Hspace, var_ket_psi:_A},
                                preserve_all=True)
                    for linmap in containing_hilbert_space_linmap_sets(_A):
                        # If the other op is in any Hilbert space linear 
                        # mappings, also prove closure within the
                        # specific linear mapping set.
                        _Hspace, _X = linmap.operands
                        op_closure_thm.instantiate(
                            {c:_c, Hspace:_Hspace, X:_X, A:_A},
                            preserve_all=True)
                    return thm.instantiate({c:_c, A:_A})

                # Next, handle the ket-bra case.
                if isinstance(op2, Bra):
                    thm = None
                    _varphi = op2.operand
                    for _Hspace in yield_known_hilbert_spaces(op1):
                        for _X in yield_known_hilbert_spaces(Ket(_varphi)):
                            # Prove linear map membership while we are
                            # at it.
                            qmult_ket_bra_is_op.instantiate(
                                    {Hspace:_Hspace, X:_X, var_ket_psi:op1,
                                     varphi:_varphi}, preserve_all=True)
                            used_Hspaces = (_Hspace, _X)
                            thm = qmult_ket_bra_in_QmultCodomain
                        if thm is None:
                            raise NotImplementedError(
                                    "Bra, %s, with no known Hilbert space "
                                    "membership for the corresponding Ket. "
                                    "Cannot prove %s membership in %s"%
                                    (op2, element, QmultCodomain))
                    if thm is not None:
                        # Just choose any valid Hilbert spaces (the 
                        # last used one will do) for the QmultCodomain
                        # membership proof.
                        _Hspace, _X = used_Hspaces
                        return thm.instantiate(
                                {Hspace:_Hspace, X:_X,
                                 varphi:_varphi, var_ket_psi:op1})

                # If the first op is a bra, let's make sure we
                # know it is a linear map.
                if isinstance(op1, Bra):
                    # By proving the bra is in QmultCodomain, we
                    # get that it is a linear map as a side-effect.
                    QmultCodomain.membership_object(Qmult(op1)).conclude()
                
                # Next, handle the op-ket case.
                # TODO: handle the ket-ket case.
                thm = None
                for _Hspace in yield_known_hilbert_spaces(op2):
                    for linmap in containing_hilbert_space_linmap_sets(op1):
                        if linmap.from_vspace == _Hspace:
                            _X = linmap.to_vspace
                            # Prove membership in the target space
                            # while we are at it.
                            qmult_op_ket_is_ket.instantiate(
                                    {Hspace:_Hspace, X:_X, A:op1,
                                     var_ket_psi:op2}, preserve_all=True)
                            used_linmap = linmap
                            thm = qmult_op_ket_in_QmultCodomain
                if thm is not None:
                    # Just choose any valid linmap (the last used one
                    # will do) for the QmultCodomain membership proof.
                    _Hspace, _X = used_linmap.operands
                    return thm.instantiate(
                            {Hspace:_Hspace, X:_X, A:op1, var_ket_psi:op2})
                
                # Finally handle the op-op case.
                thm = None
                for linmap1 in containing_hilbert_space_linmap_sets(op1):
                    for linmap2 in containing_hilbert_space_linmap_sets(op2):
                        if linmap1.from_vspace == linmap2.to_vspace:
                            _Hspace = linmap2.from_vspace
                            _X = linmap1.from_vspace
                            _Y = linmap1.to_vspace
                            # Prove linear map membership while we are
                            # at it.
                            qmult_op_op_is_op.instantiate(
                                    {Hspace:_Hspace, X:_X, Y:_Y,
                                     A:op1, B:op2}, preserve_all=True)
                            used_linmaps = (linmap1, linmap2)
                            thm = qmult_op_op_in_QmultCodomain
                if thm is not None:
                    # Just choose any valid linmaps (the last used ones 
                    # will do) for the QmultCodomain membership proof.
                    linmap1, linmap2 = used_linmaps
                    _Hspace = linmap2.from_vspace
                    _X = linmap1.from_vspace
                    _Y = linmap1.to_vspace
                    return thm.instantiate(
                            {Hspace:_Hspace, X:_X, Y:_Y, A:op1, B:op2})    
            
                raise UnsatisfiedPrerequisites(
                        "Binary Qmult operand membership is not known "
                        "to produce a well-formed Qmult: %s"%element)
            
            else:
                # n-ary Qmult closure
                # Decompose an n-ary operation to a binary operation.
                if not isinstance(element.operands[-1], ExprRange):
                    _A = element.operands[:-1]
                    _B = element.operands[-1]
                    _m = _A.num_elements()
                else:
                    # There is an ExprRange at the end.  Split off
                    # the last entry and try again.
                    if element.operands[-1:].num_elements() == 0:
                        raise NotImplementedError(
                                "Empty ExprRange at the end of the Qmult "
                                "is not handled; why not simplify the Qmult "
                                "before proving it is well-formed")
                    expr_range = element.operands[-1]
                    partition_idx = subtract(expr_range.true_end_index, one)
                    partition = element.inner_expr().operands[-1].partition(
                            partition_idx)
                    membership = InClass(partition.rhs, QmultCodomain)
                    if not membership.proven():
                        QmultCodomain.membership_object(
                                partition.rhs).conclude()
                    membership = membership.prove()
                    return partition.sub_left_side_into(membership)
                multi_def = multi_qmult_def.instantiate({m:_m, A:_A, B:_B},
                                                        preserve_all=True)
                # Prove the binary case then substitute.
                binary_membership = InClass(multi_def.rhs, QmultCodomain)
                if not binary_membership.proven():
                    QmultCodomain.membership_object(
                            multi_def.rhs).conclude()
                binary_membership = binary_membership.prove()
                # We need to propogate the side-effect memberships.
                _rhs = multi_def.rhs
                for _Hspace in yield_known_hilbert_spaces(_rhs):
                    multi_def.sub_left_side_into(InSet(_rhs, _Hspace))
                for linmap in containing_hilbert_space_linmap_sets(_rhs):                    
                    multi_def.sub_left_side_into(InSet(_rhs, linmap))                    
                return multi_def.sub_left_side_into(binary_membership)
        else:
            # The element is not a Qmult.
            
            # Handle bras
            if isinstance(element, Bra):
                thm = None
                _varphi = element.operand
                #Ket(_varphi).deduce_in_vec_space(field=Complex)
                for _Hspace in yield_known_hilbert_spaces(Ket(_varphi)):
                    # Prove membership in the target space
                    # while we are at it.
                    bra_is_linmap.instantiate(
                            {Hspace:_Hspace, varphi:_varphi},
                            preserve_all=True)
                    used_Hspace = _Hspace
                    thm = bra_in_QmultCodomain
                if thm is not None:
                    # Just choose any valid Hilbert space (the last
                    # used one will do) for the QmultCodomain 
                    # membership proof.
                    _Hspace = used_Hspace
                    return thm.instantiate({Hspace:_Hspace,varphi:_varphi})
                raise NotImplementedError(
                        "Bra, %s, with no known Hilbert space "
                        "membership for the corresponding Ket. "
                        "Cannot prove %s membership in %s"%
                        (element, self, QmultCodomain))                
            
            # Handle complex numbers as as special case
            # (first, soft attempt).
            if InSet(element, Complex).proven():
                # Complex elements are in QmultCodomain
                return complex_in_QmultCodomain.instantiate({c:element})

            for _attempt in (0, 1):
                # Handle kets
                for _Hspace in HilbertSpaces.yield_known_hilbert_spaces(
                            element):
                    return ket_in_QmultCodomain.instantiate(
                            {Hspace:_Hspace, var_ket_psi:element})
                
                # Handle linear maps
                for linmap in containing_hilbert_space_linmap_sets(element):
                    _Hspace, _X = linmap.operands
                    return op_in_QmultCodomain.instantiate(
                            {Hspace:linmap.from_vspace, X:_X, A:element})

                if _attempt==0:
                    # If all else fails, try to deduce that the element 
                    # is in a vector space.  This is useful for 
                    # operators as well as kets since matrix spaces and
                    # linear map sets are  vector spaces (though not 
                    # inner product spaces, so they aren't confused 
                    # with kets fortunately).
                    if hasattr(element, 'deduce_in_vec_space'):
                        element.deduce_in_vec_space(field=Complex)
                    else:
                        break # No need for a second attempt.
            
            # Second attempt to prove the element is complex.
            try:
                deduce_in_number_set(element, Complex)
                # Complex elements are in QmultCodomain
                return complex_in_QmultCodomain.instantiate({c:element})
            except (ProofFailure, NotImplementedError):
                pass

        raise UnsatisfiedPrerequisites(
                "%s is not known to be a complex number, vector in a "
                "vector space over complex numbers, or a linear "
                "mapping from one such vector space to another"
                %(element))
                
                
def containing_hilbert_space_linmap_sets(qobj):
    '''
    Generate any LinMap expressions representing sets of linear maps 
    between vectors spaces over complex fields (Hilbert spaces) which
    contain the given 'qobj'.
    '''
    from proveit.linear_algebra.inner_products.hilbert_spaces import (
            deduce_as_hilbert_space)
    # Prove the membership of qobj in Q* to prove
    # the side-effect linear map membership as well.
    #QmultCodomain.membership_object(qobj).conclude()
    for qobj in (qobj, Qmult(qobj)):
        for linmap_membership in InClass.yield_known_memberships(
                qobj, domain_type=LinMap._operator_):
            linmap = linmap_membership.domain
            for vec_space in linmap.operands:
                deduce_as_hilbert_space(vec_space)
            if all(InClass(V, HilbertSpaces).proven() for V 
                   in linmap.operands):
                yield linmap
