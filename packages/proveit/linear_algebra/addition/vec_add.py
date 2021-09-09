from proveit import (Literal, ExprRange, 
                     UnsatisfiedPrerequisites, relation_prover)
from proveit import a, b, n, x, y, K, V
from proveit.core_expr_types import a_1_to_n, x_1_to_n
from proveit.abstract_algebra import GroupAdd
from proveit.linear_algebra import VecSpaces


class VecAdd(GroupAdd):
    '''
    The VecAdd operation is the default for the addition of vectors
    in a vector space.
    '''
    
    _operator_ = Literal(string_format='+', theory=__file__)
    
    def __init__(self, *operands, styles=None):
        GroupAdd.__init__(self, VecAdd._operator_,
                          operands, styles=styles)
        self.terms = self.operands

    @relation_prover
    def deduce_in_vec_space(self, vec_space=None, *, field,
                            **defaults_config):
        '''
        Prove that this linear combination of vectors is in a vector
        space.  The vector space may be specified or inferred via known
        memberships.  A field for the vector space must be specified.
        '''
        from proveit.linear_algebra import ScalarMult
        
        terms = self.terms
        if vec_space is None:
            # We need to find a vector space that is common to
            # all of the terms.
            candidate_vec_spaces = None
            for term in terms:
                term_vec_spaces = set(VecSpaces.yield_known_vec_spaces(
                        term, field=field))
                if isinstance(term, ScalarMult):
                    term_vec_spaces.update(VecSpaces.yield_known_vec_spaces(
                        term.scaled, field=field))
                if candidate_vec_spaces is None:
                    candidate_vec_spaces = term_vec_spaces
                else:
                    candidate_vec_spaces.intersection_update(term_vec_spaces)
            try:
                vec_space = next(iter(candidate_vec_spaces))
            except StopIteration:
                # No known common vector space membership over the 
                # specified field.
                raise UnsatisfiedPrerequisites(
                        "%s is not known to be a vector in a vector "
                        "space over %s"%(self.scaled, field))
        all_scaled = all((isinstance(term, ScalarMult)
                          or (isinstance(term, ExprRange) and
                              isinstance(term.body, ScalarMult)))
                         for term in terms)
        if all_scaled:
            # Use a linear combination theorem since everything
            # is scaled.
            from proveit.linear_algebra.scalar_multiplication import (
                    binary_lin_comb_closure, lin_comb_closure)
            if terms.is_double():
                # Special linear combination binary case
                _a, _b = terms[0].scalar, terms[1].scalar
                _x, _y = terms[0].scaled, terms[1].scaled
                return binary_lin_comb_closure.instantiate(
                        {K:field, V:vec_space, a:_a, b:_b, x:_x, y:_y})
            else:
                # General linear combination case
                _a = []
                _x = []
                for term in terms:
                    if isinstance(term, ExprRange):
                        _a.append(ExprRange(term.parameter, term.body.scalar,
                                            term.start_index, term.end_index))
                        _x.append(ExprRange(term.parameter, term.body.scaled,
                                            term.start_index, term.end_index))
                    else:
                        _a.append(term.scalar)
                        _x.append(term.scaled)
                _n = terms.num_elements()
                return lin_comb_closure.instantiate(
                        {n:_n, K:field, V:vec_space, a:_a, x:_x})
        else:
            # Use a vector addition closure theorem.
            from . import binary_closure, closure
            if terms.is_double():
                # Special binary case
                return binary_closure.instantiate(
                        {K:field, V:vec_space, x:terms[0], y:terms[1]})
            else:
                # General case
                _n = terms.num_elements()
                return closure.instantiate(
                        {n:_n, K:field, V:vec_space, x:terms})                
