from proveit import (defaults, Literal, Operation, ProofFailure, 
                     relation_prover, equality_prover)
# from proveit.numbers.number_sets import Integer, Real
from proveit import a, b, c, i, j, x, L
from proveit.logic import Equals, InSet, SubsetEq
from proveit.relation import TransRelUpdater
from proveit.numbers import (NumberOperation, Add, ZeroSet,
                             deduce_number_set,
                             readily_provable_number_set)

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
        (x mod L) = x where applicable and
        [(a mod L + b) mod L] = [(a + b) mod L].
        '''
        from . import (int_mod_elimination, real_mod_elimination,
                       redundant_mod_elimination, 
                       redundant_mod_elimination_in_sum)
        from proveit.numbers import (
            NaturalPos, RealPos, Interval, IntervalCO, subtract, zero, one)
        deduce_number_set(self.dividend)
        divisor_ns = readily_provable_number_set(self.divisor)
        if (NaturalPos.readily_includes(divisor_ns) and 
                InSet(self.dividend, 
                      Interval(zero, 
                               subtract(self.divisor, one))).proven()):
            # (x mod L) = x if L in N+ and x in {0 .. L-1}
            return int_mod_elimination.instantiate(
                {x:self.dividend, L:self.divisor})
        if (RealPos.readily_includes(divisor_ns) and 
                InSet(self.dividend, 
                      IntervalCO(zero, self.divisor)).proven()):
            # (x mod L) = x if L in R+ and x in [0, L)
            return real_mod_elimination.instantiate(
                {x:self.dividend, L:self.divisor})
        return Mod._redundant_mod_elimination(
                self, redundant_mod_elimination, 
                redundant_mod_elimination_in_sum)

    @staticmethod
    def _redundant_mod_elimination(
            expr, mod_elimination_thm, mod_elimination_in_sum_thm):
        '''
        For use by Mod and ModAbs for shallow_simplification.
        Examples:
        If expr = Mod(Mod(a, b), b), then calling
        Mod._redundant_mod_elimination(expr,
            redundant_mod_elimination_in_modabs,
            redundant_mod_elimination_in_sum_in_modabs)
        returns Mod(a, b).
        If expr = Mod( Add(Mod(a, b), c), b ) = ((a mod b) + c) mod b,
        then calling
        Mod._redundant_mod_elimination(expr,
            redundant_mod_elimination_in_modabs,
            redundant_mod_elimination_in_sum_in_modabs)
        returns Mod(Add(a, c), b) i.e. (a+c) mod b
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
        dividend_ns = readily_provable_number_set(self.dividend)
        divisor_ns = readily_provable_number_set(self.divisor)
        int_dividend = Integer.readily_includes(dividend_ns)
        if (int_dividend and NaturalPos.readily_includes(divisor_ns)):
            return mod_natpos_in_interval.instantiate(
                {a: self.dividend, b: self.divisor})
        elif (int_dividend and Integer.readily_includes(divisor_ns)):
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
        import proveit.numbers.modular as mod_pkg
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
        
        thm = None
        if number_set == ZeroSet:
            divisor_ns = readily_provable_number_set(self.divisor)
            if Integer.readily_includes(divisor_ns):
                thm = mod_pkg.mod_in_zero_set_int
            else:
                thm = mod_pkg.mod_in_zero_set
        elif number_set == Integer:
            thm = mod_pkg.mod_int_closure
        elif number_set == Natural:
            thm = mod_pkg.mod_int_to_nat_closure
        elif number_set == Real:
            thm = mod_pkg.mod_real_closure
        if thm is not None:
            return thm.instantiate({a: self.dividend, b: self.divisor})

        raise NotImplementedError(
            "'Mod.deduce_in_number_set()' not implemented for the %s set" 
            % str(number_set))

    def readily_provable_number_set(self):
        '''
        Return the most restrictive number set we can readily
        prove contains the evaluation of this number operation.
        '''
        from proveit.numbers import (zero, one, Interval, IntervalCO, 
                                     Abs, subtract, NaturalPos, Integer)
        _b = self.divisor
        # from number_sets import deduce_in_integer, deduce_in_real
        dividend_ns = readily_provable_number_set(self.dividend)
        if dividend_ns == ZeroSet:
            # 0 mod N = 0
            return ZeroSet
        divisor_ns = readily_provable_number_set(self.divisor)
        int_dividend = Integer.readily_includes(dividend_ns)
        if (int_dividend and NaturalPos.readily_includes(divisor_ns)):
            return Interval(zero, subtract(_b, one))
        elif (int_dividend and Integer.readily_includes(divisor_ns)):
            # if the operands are integers, then we can deduce that
            # a mod b is an integer in the set {0,1,...,(b-1)}
            return Interval(zero, subtract(Abs(_b), one))
        else:
            # if the operands are reals, then we can deduce that
            # a mod b is in half-open real interval [0, b)
            return IntervalCO(zero, _b)
