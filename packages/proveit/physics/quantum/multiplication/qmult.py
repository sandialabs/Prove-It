from proveit import (Operation, Literal, Lambda, ExprRange,
                     UnsatisfiedPrerequisites,
                     prover, equality_prover)
from proveit import b, c, f, i, j, m, n, A, B, C, M, Q, X, Y
from proveit.logic import InSet, ClassMembership, InClass
from proveit.numbers import Complex, subtract, one
from proveit.abstract_algebra.generic_methods import (
        apply_association_thm, apply_disassociation_thm)
from proveit.linear_algebra import (VecSpaces, VecAdd, VecSum, LinMap,
                                    MatrixSpace)

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
    
    def __init__(self, *operands, styles=None):
        Operation.__init__(self, Qmult._operator_, operands,
                           styles=styles)
    
    def string(self, **kwargs):    
        if self.operands.is_single():
            # Single operand: wrap it in square braces to show
            # we are treating it as an operator (a function).
            return r'\left[' + self.operand.string() + r'\right]'
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

    @equality_prover('associated', 'associate')
    def association(self, start_idx, length, *, field=None, 
                    **defaults_config):
        '''
        Given a valid Qmult operation (valid sequence of bras, kets,
        and/or quantum operations), deduce that this expression is equal 
        to a form in which operands in the
        range [start_idx, start_idx+length) are grouped together.
        For example, (A B ... Y Z) = (A B ... (L ... M) ⊗ ... ⊗ Y ⊗ Z).
        '''
        from . import qmult_association
        eq = apply_association_thm(
            self, start_idx, length, qmult_association)
        return eq.with_wrapping_at()

    @equality_prover('disassociated', 'disassociate')
    def disassociation(self, idx, *, field=None, 
                       **defaults_config):
        '''
        Given a valid Qmult operation (valid sequence of bras, kets,
        and/or quantum operations), deduce that this expression is equal 
        to a form in which the operand
        at index idx is no longer grouped together.
        range [start_idx, start_idx+length) are grouped together.
        For example, (A B ... (L ... M) ⊗ ... ⊗ Y ⊗ Z) = (A B ... Y Z).
        '''
        from . import qmult_disassociation
        eq = apply_disassociation_thm(
                self, idx, qmult_disassociation)
        return eq.with_wrapping_at()

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
                    {f:_f, Q:_Q, j:_j, m:_m, n:_n, b:_b,
                     A:_A, B:_B, C:_C})
            return impl.derive_consequent().with_wrapping_at()
        else:
            raise ValueError(
                "Don't know how to distribute tensor product over " +
                str(sum_factor.__class__) + " factor")

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

    @prover
    def conclude(self, **defaults_config):
        '''
        Prove that the 'element' is in the QmultCodomain
        (e.g., that a Qmult is well-formed).
        '''
        from proveit.physics.quantum import Hspace
        from proveit.physics.quantum import var_ket_psi, var_bra_varphi
        from proveit.physics.quantum.multiplication import QmultCodomain
        from . import (
                qmult_complex_left_closure, qmult_complex_right_closure,
                qmult_complex_ket_closure, qmult_ket_complex_closure,
                qmult_complex_op_closure, qmult_op_complex_closure,
                complex_in_QmultCodomain,
                qmult_op_ket_is_ket, qmult_op_ket_in_QmultCodomain,
                qmult_ket_bra_is_op, qmult_ket_bra_in_QmultCodomain,
                qmult_op_op_is_op, qmult_op_op_in_QmultCodomain,
                qmult_matrix_is_linmap, qmult_matrix_in_QmultCodomain,
                qmult_op_is_linmap, qmult_op_in_QmultCodomain,
                ket_in_QmultCodomain, bra_in_QmultCodomain,
                op_in_QmultCodomain,
                multi_qmult_def
                )
        element = self.element
        
        if isinstance(element, Qmult):
            if element.num_entries() == 0:
                raise ValueError("Qmult with no operands is not defined")
                
            elif element.operands.is_single():
                # Unary Qmult closure
                op = element.operand
                
                # Handle unary Qmult on a matrix.
                if op in MatrixSpace.known_memberships:
                    mspace_memberships = MatrixSpace.known_memberships[op]
                    thm = None
                    for mspace_membership in mspace_memberships:
                        mspace = mspace_membership.domain
                        _m, _n = mspace.operands
                        # Prove linear map membership while we are
                        # at it.
                        qmult_matrix_is_linmap.instantiate(
                                {m:_m, n:_n, M:op})
                        used_mspace = mspace
                        thm = qmult_matrix_in_QmultCodomain
                    if thm is not None:
                        # Choose any valid matrix space (the last used 
                        # ones will do) for the QmultCodomain membership
                        # proof.
                        _m, _n = used_mspace.operands
                        return thm.instantiate(
                                {m:_m, n:_n, M:op})

                # Handle unary Qmult on a linear map.
                thm = None
                for linmap in containing_hilbert_space_linmap_sets(op):
                    _Hspace, _X = linmap.operands
                    # Prove membership in the target space
                    # while we are at it.
                    qmult_op_is_linmap.instantiate(
                            {Hspace:_Hspace, X:_X, A:op})
                    used_linmap = linmap
                    thm = qmult_op_in_QmultCodomain
                if thm is not None:
                    # Just choose any valid linmap (the last used one
                    # will do) for the QmultCodomain membership proof.
                    _Hspace, _X = used_linmap.operands
                    return thm.instantiate({Hspace:_Hspace, X:_X, A:op})

                raise NotImplementedError("No defined/known unary operation "
                                          "of Qmult on %s"%element)
                        
            elif element.operands.is_double():
                # Binary Qmult closure
                op1, op2 = element.operands
                
                # If either operand is a Qmult, prove QmultCodomain
                # closure on it to derive complex, vector space, or 
                # linear map membership(s) as side-effects which will
                # be useful below.
                if InSet(op1, Qmult):
                    InClass(op1, QmultCodomain).prove()
                if InSet(op2, Qmult):
                    InClass(op2, QmultCodomain).prove()
                
                # First handle the case where one of the operands is
                # complex.
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
                    for _Hspace in VecSpaces.yield_known_vec_spaces(
                            _A, field=Complex):
                        # If the other op is in any vector space over 
                        # Complex numbers (Hilbert spaces) also 
                        # prove closure within the Hilbert space.
                        return ket_closure_thm.instantiate(
                                {c:_c, Hspace:_Hspace, var_ket_psi:_A})
                    for linmap in containing_hilbert_space_linmap_sets(_A):
                        # If the other op is in any Hilbert space linear 
                        # mappings, also prove closure within the
                        # specific linear mapping set.
                        _Hspace, _X = linmap.operands
                        op_closure_thm.instantiate(
                            {c:_c, Hspace:_Hspace, X:_X, A:_A})
                    return thm.instantiate({X:op1, c:op2})
                
                # Next, handle the op-ket case.
                thm = None
                for _Hspace in VecSpaces.yield_known_vec_spaces(
                        op2, field=Complex):
                    for linmap in containing_hilbert_space_linmap_sets(op1):
                        if linmap.from_vspace == _Hspace:
                            _X = linmap.to_vspace
                            # Prove membership in the target space
                            # while we are at it.
                            qmult_op_ket_is_ket.instantiate(
                                    {Hspace:_Hspace, X:_X, A:op1,
                                     var_ket_psi:op2})
                            used_linmap = linmap
                            thm = qmult_op_ket_in_QmultCodomain
                if thm is not None:
                    # Just choose any valid linmap (the last used one
                    # will do) for the QmultCodomain membership proof.
                    _Hspace, _X = used_linmap.operands
                    return thm.instantiate(
                            {Hspace:_Hspace, X:_X, A:op1, var_ket_psi:op2})
    
                # Next, handle the ket-bra case.
                thm = None
                for _X in VecSpaces.yield_known_vec_spaces(
                        op1, field=Complex):
                    for linmap in containing_hilbert_space_linmap_sets(op1):
                        if linmap.to_vspace == Complex:
                            _Hspace = linmap.from_vspace
                            # Prove linear map membership while we are
                            # at it.
                            qmult_ket_bra_is_op.instantiate(
                                    {Hspace:_Hspace, X:_X, var_ket_psi:op1,
                                     var_bra_varphi:op2})
                            used_X = _X
                            used_linmap = linmap
                            thm = qmult_ket_bra_in_QmultCodomain
                if thm is not None:
                    # Just choose any valid linmap (the last used one 
                    # will do) for the QmultCodomain membership proof.
                    _X = used_X
                    _Hspace = used_linmap.from_vspace
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
                                     A:op1, B:op2})
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
                    _m = _A.num_elements
                else:
                    # There is an ExprRange at the end.  Split off
                    # the last entry and try again.
                    if element.operands[-1:].num_elements() == 0:
                        raise NotImplementedError(
                                "Empty ExprRange at the end of the Qmult "
                                "is not handled; why not simplify the Qmult "
                                "before proving it is well-formed")
                    expr_range = element.operands[-1]
                    partition_idx = subtract(expr_range.end_index, one)
                    partition = element.inner_expr().operands[-1].partition(
                            partition_idx)
                    membership = InClass(partition.rhs, QmultCodomain).prove()
                    return partition.sub_left_side_into(membership)
                multi_def = multi_qmult_def.instantiate({m:_m, A:_A, B:_B})
                # Prove the binary case then substitute.
                binary_membership = InClass(multi_def.rhs, 
                                            QmultCodomain).prove()
                return multi_def.sub_left_side_into(binary_membership)
        else:
            # Handle complex numbers as as special case.
            if InSet(element, Complex).proven():
                # Complex elements are in QmultCodomain
                return complex_in_QmultCodomain.instantiate({c:element})
            
            # Handle kets
            for _Hspace in VecSpaces.yield_known_vec_spaces(
                        element, field=Complex):
                return ket_in_QmultCodomain.instantiate(
                        {Hspace:_Hspace, var_ket_psi:element})
            
            # Handle linear maps
            for linmap in containing_hilbert_space_linmap_sets(element):
                if linmap.to_vspace == Complex:
                    return bra_in_QmultCodomain.instantiate(
                            {Hspace:linmap.from_vspace, A:element})
                else:
                    _Hspace, _X = linmap.operands
                    return op_in_QmultCodomain.instantiate(
                            {Hspace:linmap.from_vspace, X:_X, A:element})

            raise UnsatisfiedPrerequisites(
                    "%s is not known to be a complex number, vector in a "
                    "vector space over complex numbers, or a linear "
                    "mapping from one such vector space to another")
                
                
def containing_hilbert_space_linmap_sets(qobj):
    '''
    Generate any LinMap expressions representing sets of linear maps 
    between vectors spaces over complex fields (Hilbert spaces) which
    contain the given 'qobj'.
    '''
    known_linmap_memberships = LinMap.known_memberships
    if qobj in known_linmap_memberships:
        for linmap in known_linmap_memberships[qobj]:
            if all(InClass(V, VecSpaces(Complex)).proven() for V 
                   in linmap.operands):
                yield linmap
