from proveit import KnownTruth, USE_DEFAULTS
from proveit.logic import Equals
from proveit.number import Less, LessEq, Greater, GreaterEq, frac, zero, one, two
from proveit._common_ import a, x, y

class NumberRelation:
    def __init__(self, relation):
        if (not isinstance(relation, KnownTruth) or
                not (isinstance(relation.expr, Equals) or
                     isinstance(relation.expr, Less) or
                     isinstance(relation.expr, LessEq))):
            raise ValueError("'relation' must be a Judgement for an Equals, "
                             "Less, or LessEq statement.")
        self.relation = relation
    
    def _repr_html_(self):
        return self.relation._repr_html_()
    
    def _update(self, new_relation):
        self.relation = new_relation
        return self.relation
    
    def mult_left(self, multiplier, assumptions=USE_DEFAULTS):
        from proveit.number.multiplication._theorems_ import (
                mult_left_eq, mult_pos_left_less, mult_nonneg_left_less,
                mult_pos_left_lesseq, mult_neg_left_less, mult_nonpos_left_less,
                mult_neg_left_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(mult_left_eq.instantiate(
                    {a:multiplier, x:rel.lhs, y:rel.rhs}, 
                    assumptions=assumptions))
        elif isinstance(self.relation.expr, Less):
            if Greater(multiplier, zero).proven(assumptions):
                return self._update(mult_pos_left_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif Less(multiplier, zero).proven(assumptions):
                return self._update(mult_neg_left_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(mult_nonneg_left_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(mult_nonpos_left_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            else:
                raise Exception("Cannot 'mult_left' a Less relation without "
                                "knowing the multiplier's relation with zero.")
        elif isinstance(self.relation.expr, LessEq):
            if GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(mult_pos_left_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(mult_neg_left_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))      
            else:
                raise Exception("Cannot 'mult_left' a LessEq relation without "
                                "knowing the multiplier's relation with zero.")
        assert False, "Must be Equals, Less, or LessEq relation"
        
    def mult_right(self, multiplier, assumptions=USE_DEFAULTS):
        from proveit.number.multiplication._theorems_ import (
                mult_right_eq, mult_pos_right_less, mult_nonneg_right_less,
                mult_pos_right_lesseq, mult_neg_right_less, mult_nonpos_right_less,
                mult_neg_right_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(mult_right_eq.instantiate(
                    {a:multiplier, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        elif isinstance(rel, Less):
            if Greater(multiplier, zero).proven(assumptions):
                return self._update(mult_pos_right_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif Less(multiplier, zero).proven(assumptions):
                return self._update(mult_neg_right_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(mult_nonneg_right_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(mult_nonpos_right_less.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            else:
                raise Exception("Cannot 'mult_right' a Less relation without "
                                "knowing the multiplier's relation with zero.")
        elif isinstance(rel, LessEq):
            if GreaterEq(multiplier, zero).proven(assumptions):
                return self._update(mult_pos_right_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif LessEq(multiplier, zero).proven(assumptions):
                return self._update(mult_neg_right_lesseq.instantiate(
                        {a:multiplier, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))           
            else:
                raise Exception("Cannot 'mult_right' a LessEq relation without "
                                "knowing the multiplier's relation with zero.")
        assert False, "Must be Equals, Less, or LessEq relation"
    
    def divide(self, divisor, assumptions=USE_DEFAULTS):
        from proveit.number.division._theorems_ import (
                div_eq, div_pos_less, div_neg_less, div_pos_lesseq, div_neg_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(div_eq.instantiate(
                    {a:divisor, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        elif isinstance(self.relation.expr, Less):
            if Greater(divisor, zero).proven(assumptions):
                return self._update(div_pos_less.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif Less(divisor, zero).proven(assumptions):
                return self._update(div_neg_less.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            else:
                raise Exception("Cannot 'divide' a Less relation without "
                                "knowing whether the divisor is greater than "
                                "or less than zero.")
        elif isinstance(self.relation.expr, LessEq):
            if Greater(divisor, zero).proven(assumptions):
                return self._update(div_pos_lesseq.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif Less(divisor, zero).proven(assumptions):
                return self._update(div_neg_lesseq.instantiate(
                        {a:divisor, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))         
            else:
                raise Exception("Cannot 'divide' a LessEq relation without "
                                "knowing whether the divisor is greater than "
                                "or less than zero.")
        assert False, "Must be Equals, Less, or LessEq relation"    
    
    def add_left(self, addend, assumptions=USE_DEFAULTS):
        from proveit.number.addition._theorems_ import (
                add_left_eq, add_left_less, add_left_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(add_left_eq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        elif isinstance(self.relation.expr, Less):
            return self._update(add_left_less.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        elif isinstance(self.relation.expr, LessEq):
            return self._update(add_left_lesseq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        assert False, "Must be Equals, Less, or LessEq relation"
    
    def add_right(self, addend, assumptions=USE_DEFAULTS):
        from proveit.number.addition._theorems_ import (
                add_right_eq, add_right_less, add_right_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(add_right_eq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        elif isinstance(self.relation.expr, Less):
            return self._update(add_right_less.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        elif isinstance(self.relation.expr, LessEq):
            return self._update(add_right_lesseq.instantiate(
                    {a:addend, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        assert False, "Must be Equals, Less, or LessEq relation"
    
    def exponentiate(self, exponent, assumptions=USE_DEFAULTS):
        from proveit.number.exponentiation._theorems_ import (
                exp_eq, exp_pos_less, exp_nonneg_less, exp_neg_less,
                exp_nonpos_less, exp_pos_lesseq, exp_nonneg_lesseq, 
                exp_neg_lesseq, exp_nonpos_lesseq)
        rel = self.relation.expr
        if isinstance(rel, Equals):
            return self._update(exp_eq.instantiate(
                    {a:exponent, x:rel.lhs, y:rel.rhs},
                    assumptions=assumptions))
        elif isinstance(rel, Less):
            if Greater(exponent, zero).proven(assumptions):
                return self._update(exp_pos_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif Less(exponent, zero).proven(assumptions):
                return self._update(exp_neg_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif GreaterEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonneg_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif LessEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonpos_less.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            else:
                raise Exception("Cannot 'exponentiate' a Less relation without "
                                "knowing the exponent's relation with zero")
        elif isinstance(rel, LessEq):
            if Greater(exponent, zero).proven(assumptions):
                return self._update(exp_pos_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif Less(exponent, zero).proven(assumptions):
                return self._update(exp_neg_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif GreaterEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonneg_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))
            elif LessEq(exponent, zero).proven(assumptions):
                return self._update(exp_nonpos_lesseq.instantiate(
                        {a:exponent, x:rel.lhs, y:rel.rhs},
                        assumptions=assumptions))       
            else:
                raise Exception("Cannot 'exponentiate' a Less relation without "
                                "knowing the exponent's relation with zero")
        assert False, "Must be Equals, Less, or LessEq relation"        
        
    def square(self, assumptions=USE_DEFAULTS):
        return self.exponentiate(two, assumptions)

    def square_root(self, assumptions=USE_DEFAULTS):
        new_rel = self.exponentiate(frac(one, two), assumptions)  
        new_rel.innerExpr().lhs.withStyles(exponent='radical')
        new_rel.innerExpr().rhs.withStyles(exponent='radical')
        return new_rel