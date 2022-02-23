from proveit import Function, Literal, relation_prover
from proveit.numbers import deduce_number_set

class Log(Function):
    # operator of the Log operation.
    _operator_ = Literal(string_format='log', latex_format=r'\textrm{log}',
                         theory=__file__)    
    
    def __init__(self, base, antilog, *, styles=None):
        Function.__init__(self, Log._operator_, (base, antilog),
                          styles=styles)
        self.base = base
        self.antilog = antilog

    def string(self, **kwargs):
        return Log._operator_.string() + "_%s(%s)"%(
                self.base.string(), self.antilog.string())

    def latex(self, **kwargs):
        return Log._operator_.latex() + r"_%s\left(%s\right)"%(
                self.base.latex(), self.antilog.latex())

    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        '''
        Attempt to prove that the logarithmic expression 'self' is
        in the given number set 'number_set'. May require user to
        previously show or assume that the Log base is not 1.
        Currently implemented only for the general case, giving
        Log_a(b) in Real when 'a' and 'b' both in RealPos and 'a' != 1.
        This can be augmented in near future.
        '''
        from proveit import a, b
        from proveit.logic import InSet, NotEquals
        from proveit.numbers.logarithms import log_real_pos_real_closure

        from proveit.numbers import zero, Real

        deduce_number_set(self.base)
        deduce_number_set(self.antilog)
        if number_set == Real:
            return log_real_pos_real_closure.instantiate(
                {a: self.base, b: self.antilog})

        # we can do more/better but that's enough for right now

        raise NotImplementedError(
            "'Log.deduce_in_number_set()' not implemented for the "
            " number set {0}. Try deducing in Real instead?".
            format(number_set))

    @relation_prover
    def deduce_number_set(self, **defaults_config):
        '''
        Prove membership of this Log expression in the most
        restrictive standard number set we can readily know.
        Currently just implemented for Reals, but should be able
        to augment this to allow more precise placement in
        RealPos vs. RealNeg for suitable base/antilog combinations.
        '''
        from proveit.numbers import Real, RealPos
        base_ns = deduce_number_set(self.base).domain
        antilog_ns = deduce_number_set(self.antilog).domain
        if RealPos.includes(base_ns) and RealPos.includes(antilog_ns):
            return self.deduce_in_number_set(Real)
        return self.deduce_in_number_set(Complex)
