from proveit import KnownTruth, USE_DEFAULTS
from proveit.logic import Equals, NotEquals
from proveit.number import Less, LessEq, Greater, GreaterEq, frac, zero, one, two
from proveit._common_ import a, x, y

class NumberRelation:
    def __init__(self, relation):
        if (not isinstance(relation, KnownTruth) or
                not (isinstance(relation.expr, NotEquals) or
                     isinstance(relation.expr, Equals) or
                     isinstance(relation.expr, Less) or
                     isinstance(relation.expr, LessEq))):
            raise ValueError("'relation' must be a Judgement for an Equals, "
                             "Less, or LessEq statement.")
        self.relation = relation
    
    def _repr_html_(self):
        return self.relation._repr_html_()
    
    def _update(self, relation, simplify, assumptions):
        if simplify:
            relation = relation.innerExpr().lhs.simplify(assumptions)
            relation = relation.innerExpr().rhs.simplify(assumptions)
        self.relation = relation
        return relation
    
    def left_mult_both_sides(self, multiplier, *, simplify=True, 
                             assumptions=USE_DEFAULTS):
        from proveit.number.multiplication._theorems_ import (
                left_mult_eq, left_mult_neq, left_mult_pos_less, 
                left_mult_nonneg_less, left_mult_pos_lesseq, left_mult_neg_less, 
                left_mult_nonpos_less, left_mult_neg_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(left_mult_eq.instantiate(
                    {a:multiplier, x:rel.lhs, y:rel.rhs}, 
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, NotEquals):
            return self._update(left_mult_neq.instantiate(
                    {a:multiplier, x:rel.lhs, y:rel.rhs}, 
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(self.relation.expr, Less):
            if Greater(multiplier, zero).proven(assumptions):
                return self._update(left_mult_pos_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif Less(multiplier, zero).proven(assumptions):
                return self._update(left_mult_neg_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(left_mult_nonneg_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(left_mult_nonpos_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            else:
                raise Exception(
                        "Cannot 'left_mult_both_sides' a Less relation without "
                        "knowing the multiplier's relation with zero.")
        elif isinstance(self.relation.expr, LessEq):
            if GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(left_mult_pos_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(left_mult_neg_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)      
            else:
                raise Exception(
                        "Cannot 'left_mult_both_sides' a LessEq relation without "
                        "knowing the multiplier's relation with zero.")
        assert False, "Must be Equals, NotEquals, Less, or LessEq relation"
        
    def right_mult_both_sides(self, multiplier, *, simplify=True, 
                              assumptions=USE_DEFAULTS):
        from proveit.number.multiplication._theorems_ import (
                right_mult_eq, right_mult_neq, right_mult_pos_less, 
                right_mult_nonneg_less, right_mult_pos_lesseq, right_mult_neg_less, 
                right_mult_nonpos_less, right_mult_neg_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(right_mult_eq.instantiate(
                    {a:multiplier, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, NotEquals):
            return self._update(right_mult_neq.instantiate(
                    {a:multiplier, x:rel.lhs, y:rel.rhs}, 
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, Less):
            if Greater(multiplier, zero).proven(assumptions):
                return self._update(right_mult_pos_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif Less(multiplier, zero).proven(assumptions):
                return self._update(right_mult_neg_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(right_mult_nonneg_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(right_mult_nonpos_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            else:
                raise Exception(
                        "Cannot 'right_mult_both_sides' a Less relation without "
                        "knowing the multiplier's relation with zero.")
        elif isinstance(rel, LessEq):
            if GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(right_mult_pos_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(right_mult_neg_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))           
            else:
                raise Exception(
                        "Cannot 'right_mult_both_sides' a LessEq relation without "
                        "knowing the multiplier's relation with zero.")
        assert False, "Must be Equals, NotEquals, Less, or LessEq relation"
    
    def divide_both_sides(self, divisor, *, simplify=True, assumptions=USE_DEFAULTS):
        from proveit.number.division._theorems_ import (
                div_eq, div_neq, div_pos_less, div_neg_less, 
                div_pos_lesseq, div_neg_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(div_eq.instantiate(
                    {a:divisor, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, NotEquals):
            return self._update(div_neq.instantiate(
                    {a:divisor, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(self.relation.expr, Less):
            if Greater(divisor, zero).proven(assumptions):
                return self._update(div_pos_less.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif Less(divisor, zero).proven(assumptions):
                return self._update(div_neg_less.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            else:
                raise Exception("Cannot 'divide' a Less relation without "
                                "knowing whether the divisor is greater than "
                                "or less than zero.")
        elif isinstance(self.relation.expr, LessEq):
            if Greater(divisor, zero).proven(assumptions):
                return self._update(div_pos_lesseq.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif Less(divisor, zero).proven(assumptions):
                return self._update(div_neg_lesseq.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)         
            else:
                raise Exception("Cannot 'divide' a LessEq relation without "
                                "knowing whether the divisor is greater than "
                                "or less than zero.")
        assert False, "Must be Equals, NotEquals, Less, or LessEq relation"
    
    def left_add_both_sides(self, addend, *, simplify=True, assumptions=USE_DEFAULTS):
        from proveit.number.addition._theorems_ import (
                left_add_eq, left_add_neq, left_add_less, left_add_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(left_add_eq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, NotEquals):
            return self._update(left_add_neq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(self.relation.expr, Less):
            return self._update(left_add_less.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(self.relation.expr, LessEq):
            return self._update(left_add_lesseq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        assert False, "Must be Equals, Less, or LessEq relation"
    
    def right_add_both_sides(self, addend, *, simplify=True, assumptions=USE_DEFAULTS):
        from proveit.number.addition._theorems_ import (
                right_add_eq, right_add_neq, right_add_less, right_add_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(right_add_eq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, NotEquals):
            return self._update(right_add_neq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(self.relation.expr, Less):
            return self._update(right_add_less.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(self.relation.expr, LessEq):
            return self._update(right_add_lesseq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        assert False, "Must be Equals, NotEquals, Less, or LessEq relation"
    
    def exponentiate_both_sides(self, exponent, *, simplify=True, assumptions=USE_DEFAULTS):
        from proveit.number.exponentiation._theorems_ import (
                exp_eq, exp_neq, exp_pos_less, exp_nonneg_less, exp_neg_less,
                exp_nonpos_less, exp_pos_lesseq, exp_nonneg_lesseq, 
                exp_neg_lesseq, exp_nonpos_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(exp_eq.instantiate(
                    {a:exponent, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, NotEquals):
            return self._update(exp_neq.instantiate(
                    {a:exponent, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions), simplify, assumptions)
        elif isinstance(rel, Less):
            if Greater(exponent, zero).proven(assumptions):
                return self._update(exp_pos_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif Less(exponent, zero).proven(assumptions):
                return self._update(exp_neg_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif GreaterEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonneg_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif LessEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonpos_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            else:
                raise Exception("Cannot 'exponentiate' a Less relation without "
                                "knowing the exponent's relation with zero")
        elif isinstance(rel, LessEq):
            if Greater(exponent, zero).proven(assumptions):
                return self._update(exp_pos_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif Less(exponent, zero).proven(assumptions):
                return self._update(exp_neg_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif GreaterEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonneg_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)
            elif LessEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonpos_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions), simplify, assumptions)       
            else:
                raise Exception("Cannot 'exponentiate' a Less relation without "
                                "knowing the exponent's relation with zero")
        assert False, "Must be Equals, NotEquals, Less, or LessEq relation"
        
    def square_both_sides(self, *, simplify=True, assumptions=USE_DEFAULTS):
        return self.exponentiate_both_sides(two, simplify=simplify, assumptions=assumptions)

    def square_root_both_sides(self, *, simplify=True, assumptions=USE_DEFAULTS):
        new_rel = self.exponentiate_both_sides(frac(one, two), 
                                               simplify=simplify,
                                               assumptions=assumptions)  
        new_rel.innerExpr().lhs.withStyles(exponent='radical')
        new_rel.innerExpr().rhs.withStyles(exponent='radical')
        return new_rel