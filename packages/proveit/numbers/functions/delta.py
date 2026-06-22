from proveit import (
        i, j, x, y, equality_prover, Literal, Operation,
        relation_prover, TransRelUpdater)
from proveit.logic import Equals, is_irreducible_value, NotEquals
from proveit.logic.sets import Set
from proveit.numbers import zero, one

class KroneckerDelta(Operation):
    '''
    The Kronecker delta function of i and j is equal to 1 if
    i=j or equals 0 otherwise.
    '''

    _operator_ = Literal(string_format='Kdelta', theory=__file__)

    def __init__(self, i, j, *, styles=None):
        '''
        Kronecker delta of i and j.
        '''
        Operation.__init__(self, KroneckerDelta._operator_, (i, j),
                           styles=styles)

    def string(self, **kwargs):
        return ('delta_{' + self.operands[0].string(fence=True) + ', '
                         + self.operands[1].string(fence=True) + '}')

    def latex(self, **kwargs):
        return (r'\delta_{' + self.operands[0].string(fence=True) + ', '
                         + self.operands[1].string(fence=True)) + '}'

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Return a proven simplification equation for this KroneckerDelta
        expression assuming the operands have been simplified.
        This mostly consists of evaluating the Kronecker delta function
        d(i,j) for cases where we know that i = j or i ≠ j.
        '''

        from . import kron_delta_def, kron_delta_image
        from proveit.logic.sets.enumeration import fold_singleton

        expr = self
        # For convenience in updating our equation
        eq = TransRelUpdater(self)

        _op_0 = self.operands[0]
        _op_1 = self.operands[1]

        # Calling NotEquals(_op_0, _op_1).readily_provable() further
        # below misses some obvious cases, so we try a proof first
        try:
            NotEquals(_op_0, _op_1).prove()
        except:
            pass
        
        # Now we're ready to instantiate d(i,j) using the evaluation
        # axiom for any of the following situations:
        # (1) i == j;
        # (2) i is readily provably equal to j;
        # (3) i, j irreducible and not equal
        if ((_op_0 == _op_1) or (Equals(_op_0, _op_1).readily_provable())
            or (NotEquals(_op_0, _op_1).readily_provable()) or
            (is_irreducible_value(_op_0) and is_irreducible_value(_op_1)
                and _op_0 != _op_1)):
            eq.update(kron_delta_def.instantiate({i:_op_0, j:_op_1}))

        return eq.relation # Might simply be self=self.



    @equality_prover('commuted', 'commute')
    def commutation(self, **defaults_config):
        '''
        Deduce that this KroneckerDelta function expression delta(i,j)
        is equal to the KroneckerDelta function in which the operands
        have changed order: delta(j, i).
        '''
        from . import kron_delta_commutation
        _i_sub = self.operands[0]
        _j_sub = self.operands[1]
        return kron_delta_commutation.instantiate({i:_i_sub, j:_j_sub})

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this KroneckerDelta operation.
        If we have actual values for the arguments, we can return a
        singleton set {0} or {1}, otherwise we can return the two-elem
        set {0, 1}.
        '''
        _i = self.operands[0]
        _j = self.operands[1]
        if _i == _j: return Set(one)
        if (is_irreducible_value(_i) and is_irreducible_value(_j)
           and _i != _j):
            return Set(zero)
        return Set(zero, one)

    def deduce_image_set(self, **defaults_config):
        '''
        Deduce and return the set membership claim [self in {0,1}].
        '''
        from . import kron_delta_def, kron_delta_image
        from proveit.logic.sets.enumeration import fold_singleton
        _op_0 = self.operands[0]
        _op_1 = self.operands[1]
        if _op_0 == _op_1:
            kron_delta_eval = kron_delta_def.instantiate({i:_op_0, j:_op_1})
            return fold_singleton.instantiate({x:self, y:one})
        if (is_irreducible_value(_op_0) and is_irreducible_value(_op_1)
           and _op_0 != _op_1):
            kron_delta_eval = kron_delta_def.instantiate({i:_op_0, j:_op_1})
            return fold_singleton.instantiate({x:self, y:zero})

        return kron_delta_image.instantiate({i:_op_0, j:_op_1})

    def deduce_bounds(self, **defaults_config):
        '''
        Deduce and return the bounding claim that [0 ≤ self ≤ 1].
        '''
        from . import kron_delta_bounds
        _i_sub = self.operands[0]
        _j_sub = self.operands[1]
        return kron_delta_bounds.instantiate({i:_i_sub, j:_j_sub})

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set 'number_set', attempt to prove that the
        given KroneckerDelta expression is in that number set.
        Recall that KroneckerDelta in always in the set {0,1},
        so this amounts to first deducing that this specific
        KroneckerDelta expression, which might actually be 0
        or 1, or just in {0,1} more generally, is in a subset
        of the provided number_set, then returning the desired
        InSet() judgment.
        '''
        from proveit.logic.sets import InSet, Set, SubsetEq
        from proveit.numbers import zero, one
        SubsetEq(self.deduce_image_set().rhs, number_set).prove()
        return InSet(self, number_set).prove()

