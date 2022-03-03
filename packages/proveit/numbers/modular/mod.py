from proveit import (defaults, Literal, Operation, ProofFailure, 
                     relation_prover, equality_prover)
# from proveit.numbers.number_sets import Integer, Real
from proveit import a, b, c, i, j, L
from proveit.logic import Equals, InSet, SubsetEq
from proveit.relation import TransRelUpdater
from proveit.numbers import NumberOperation, deduce_number_set, Add

class Mod(NumberOperation):
    # operator of the Mod operation.
    _operator_ = Literal(string_format='mod', latex_format=r'~\textup{mod}~',
                         theory=__file__)

    def __init__(self, dividend, divisor, *, styles=None):
        NumberOperation.__init__(self, Mod._operator_, (dividend, divisor),
                                 styles=styles)
        self.dividend = self.operands[0]
        self.divisor = self.operands[1]

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Returns a proven simplification equation for this Mod
        expression assuming the operands have been simplified.
        
        Specifically, performs reductions of the form
        [(a mod L + b) mod L] = [(a + b) mod L].
        '''
        from . import redundant_mod_elimination, redundant_mod_elimination_in_sum
        return Mod._redundant_mod_elimination(
                self, redundant_mod_elimination, 
                redundant_mod_elimination_in_sum)

    @staticmethod
    def _redundant_mod_elimination(
            expr, mod_elimination_thm, mod_elimination_in_sum_thm):
        '''
        For use by Mod and ModAbs for shallow_simplification.
        '''
        dividend = expr.dividend
        divisor = expr.divisor
        if isinstance(dividend, Mod) and dividend.divisor==divisor:
            # [(a mod b) mod b] = [a mod b]
            return mod_elimination_thm.instantiate(
                    {a:dividend.dividend, b:divisor})
        elif isinstance(dividend, Add):
            # Eliminate 'mod L' from each term.
            eq = TransRelUpdater(expr)
            _L = divisor
            mod_terms = []
            for _k, term in enumerate(dividend.terms):
                if isinstance(term, Mod) and term.divisor==_L:
                    mod_terms.append(_k)
            for _k in mod_terms:
                # Use preserve_all=True for all but the last term.
                preserve_all = (_k != mod_terms[-1])
                _a = expr.dividend.terms[:_k]
                _b = expr.dividend.terms[_k].dividend
                _c = expr.dividend.terms[_k+1:]
                _i = _a.num_elements()
                _j = _c.num_elements()
                expr = eq.update(
                        mod_elimination_in_sum_thm
                        .instantiate(
                                {i:_i, j:_j, a:_a, b:_b, c:_c, L:_L},
                                preserve_all=preserve_all))
            return eq.relation
        return Equals(expr, expr).conclude_via_reflexivity()

    # def deduce_in_interval(self, assumptions=frozenset()):
    #     from . import mod_in_interval, mod_in_interval_c_o
    #     from number_sets import deduce_in_integer, deduce_in_real
    #     try:
    #         # if the operands are integers, then we can deduce that
    #         # a mod b is in 0..(b-1)
    #         deduce_in_integer(self.operands, assumptions)
    #         return mod_in_interval.instantiate(
    #                 {a:self.dividend, b:self.divisor}).checked(assumptions)
    #     except:
    #         # if the operands are reals, then we can deduce that a mod b is in [0, b)
    #         deduce_in_real(self.operands, assumptions)
    # return mod_in_interval_c_o.instantiate({a:self.dividend,
    # b:self.divisor}).checked(assumptions)

    @relation_prover
    def deduce_in_interval(self, **defaults_config):
        '''
        Prove that the "x mod b" is in the interval [0, b).
        '''
        from . import (mod_in_interval, mod_natpos_in_interval,
                       mod_in_interval_c_o)
        from proveit.numbers import Integer, NaturalPos
        # from number_sets import deduce_in_integer, deduce_in_real
        dividend_ns = deduce_number_set(self.dividend).domain
        divisor_ns = deduce_number_set(self.divisor).domain
        int_dividend = Integer.includes(dividend_ns)
        if (int_dividend and NaturalPos.includes(divisor_ns)):
            return mod_natpos_in_interval.instantiate(
                {a: self.dividend, b: self.divisor})
        elif (int_dividend and Integer.includes(divisor_ns)):
            # if the operands are integers, then we can deduce that
            # a mod b is an integer in the set {0,1,...,(b-1)}
            return mod_in_interval.instantiate(
                {a: self.dividend, b: self.divisor})
        else:
            # if the operands are reals, then we can deduce that
            # a mod b is in half-open real interval [0, b)
            return mod_in_interval_c_o.instantiate(
                {a: self.dividend, b: self.divisor})

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Given a number set number_set (such as Integer, Real, etc),
        attempt to prove that the given Mod expression is in that number
        set using the appropriate closure theorem.
        '''
        from proveit.numbers.modular import (
            mod_int_closure, mod_int_to_nat_closure, mod_real_closure)
        from proveit.numbers import (Integer, Natural, Real,
                                     Interval, RealInterval)

        if (isinstance(number_set, Interval) or 
                isinstance(number_set, RealInterval)):
            if isinstance(number_set, Interval):
                # To prove that it is in an integer interval through
                # standard means, we'll need to know that the dividend
                # and divisor are integers.
                InSet(self.dividend, Integer).prove()
                InSet(self.divisor, Integer).prove()
            in_mod_interval = self.deduce_in_interval()
            mod_interval = in_mod_interval.domain
            if mod_interval == number_set:
                return in_mod_interval
            # To prove by standard means, 'mod_interval' must be a
            # subset of 'number_set'.
            set_relation = SubsetEq(mod_interval, number_set).prove()
            return set_relation.derive_superset_membership(self)
            
        if number_set == Integer:
            return mod_int_closure.instantiate(
                {a: self.dividend, b: self.divisor})

        if number_set == Natural:
            return mod_int_to_nat_closure.instantiate(
                {a: self.dividend, b: self.divisor})

        if number_set == Real:
            return mod_real_closure.instantiate(
                {a: self.dividend, b: self.divisor})

        raise NotImplementedError(
            "'Mod.deduce_in_number_set()' not implemented for the %s set" 
            % str(number_set))

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this expression in the most 
        restrictive standard number set we can readily know.
        '''
        return self.deduce_in_interval()

