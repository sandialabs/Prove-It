from collections import Counter
from proveit import Operation
from proveit import x, y, alpha
from proveit.logic import Equals
from proveit.abstract_algebra.generic_methods import (
        deduce_equality_via_commutation)
from .vector_spaces import VecSpaces

class VecOperation(Operation):
    '''
    Base class for operation acting on vectors.
    '''    

    def __init__(self, operator, operand_or_operands, *, styles=None):
        Operation.__init__(self, operator, operand_or_operands, styles=styles)

    def readily_factorable(self, factor):
        '''
        Return True iff 'factor' is factorable from 'self' in an
        obvious manner.
        '''
        return self == factor

    def _deduce_canonically_equal(self, rhs):
        '''
        Prove that this vector operation is equal to an expression that
        has the same canonical form.  Similar to
        NumberOperation._deduce_canonically_equal
        '''
        from proveit.linear_algebra import (
                VecAdd, VecSum, ScalarMult, TensorProd)
        lhs = self
        assert lhs.canonical_form() == rhs.canonical_form()
        equality = Equals(lhs, rhs)

        # If the rhs is the same type as the lhs and the
        # canonical forms of the operands are the same, we can
        # use direct substitution and/or a permutation for operations
        # that commute (Add and Mult).
        if isinstance(rhs, type(lhs)):
            canonical_lhs_operands = [operand.canonical_form() for operand
                                      in lhs.operands]
            canonical_rhs_operands = [operand.canonical_form() for operand
                                      in rhs.operands]
            if canonical_lhs_operands == canonical_rhs_operands:
                # Just use direct substitution and proving that
                # corresponding operands are equal.
                for lhs_operand, rhs_operand in zip(lhs.operands,
                                                    rhs.operands):
                    if lhs_operand != rhs_operand:
                        Equals(lhs_operand, rhs_operand).prove()
                return equality.conclude_via_direct_substitution()
            elif isinstance(self, VecAdd) and (
                    Counter(canonical_lhs_operands) ==
                    Counter(canonical_rhs_operands)):
                # We just need direct substitution and permutation.
                return deduce_equality_via_commutation(equality, one_side=self)

        # Since the canonical forms are the same, we should be
        # able to equate their simplifications.
        # But make sure we use the proper simplification directives
        # (mostly the default ones).
        with VecSum.temporary_simplification_directives(use_defaults=True) as sum_simps:
            with VecAdd.temporary_simplification_directives(use_defaults=True), \
                 ScalarMult.temporary_simplification_directives(use_defaults=True), \
                 TensorProd.temporary_simplification_directives(use_defaults=True):
                # Pull out index-independent factors from summations.
                sum_simps.pull_out_index_indep_factors = True
                lhs_simplification = lhs.simplification()
                rhs_simplification = rhs.simplification()
        eq_simps = Equals(lhs_simplification.rhs,
                          rhs_simplification.rhs).prove()
        return Equals.apply_transitivities([lhs_simplification,
                                            eq_simps,
                                            rhs_simplification])

    @staticmethod
    def scalar_mult_both_sides_of_equals(relation, scalar, **defaults_config):
        from proveit.linear_algebra.scalar_multiplication import scalar_mult_eq
        return scalar_mult_eq.instantiate(
                {x:relation.lhs, y:relation.rhs, alpha:scalar})


def readily_factorable(term, factor, *, pull):
    '''
    Return True iff the 'factor' can obviously be factored out of
    'term', pulling either to the 'left' or the 'right'.
    If pulling to the 'left', the factor must be at the front
    of any tensor product of vectors.  If pulling to the 'right', 
    the factor must be at the back of any tensor product of vectors.
    '''
    from proveit.numbers import one
    if term == factor or factor == one:
        return True
    if hasattr(term, 'readily_factorable'):
        return term.readily_factorable(factor, pull=pull)
    return False

def deduce_canonically_equal(expr1, expr2, *, field):
    '''
    Return the proven equality of two expressions that presumably
    involve vectos.  Temporarily set the vector space 'field' to use
    in this process.
    '''
    _orig_default_field = VecSpaces.default_field
    try:
        VecSpaces.default_field = field
        return expr1.deduce_canonically_equal(expr2)
    finally:
        VecSpaces.default_field = _orig_default_field
