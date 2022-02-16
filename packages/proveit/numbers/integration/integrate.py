from proveit import ( defaults,
        Lambda, Literal, maybe_fenced, OperationOverInstances,
        relation_prover)
from proveit.numbers import (
        zero, one, infinity, Interval, IntervalCC, IntervalCO, IntervalOC,
        IntervalOO, Neg, NumberOperation, Real, RealNeg, RealNonNeg,
        RealNonPos, RealPos)


class Integrate(OperationOverInstances):
    # operator of the Integrate operation.
    _operator_ = Literal(
        string_format='Integrate',
        latex_format=r'\int',
        theory=__file__)

    _init_argname_mapping_ = {'index_or_indices': 'instance_param_or_params',
                              'integrand': 'instance_expr'}

    # original
    # def __init__(self, index, integrand, domain, *, condition=None,
    #              conditions=None, styles=None):
    # new 20220111
    def __init__(self, index_or_indices, integrand, *, domain=None,
                 domains=None, condition=None, conditions=None,
                 styles=None, _lambda_map=None):
        r'''
        Represents a definite integral of the integrand over the
        index_or_indices over the domain, with arguments serving
        roles analogous to those for Forall arguments (found in
        logic.booleans.quantification.universality) and Sum arguments
        (found in numbers.summation):
        index_or_indices: a single instance var such as x
        integrand       : instance expression
        domain          : conditions
        Despite the generality preserved for the arguments, such
        Integrate objects are currently defined only for a single
        index and over a single continuous interval domain defined
        by a numerical set (such as Real, RealPos, etc.) or real
        interval (using IntervalCC, IntervalCO, IntervalOC, or
        IntervalOO objects).
        '''

        # original
        # OperationOverInstances.__init__(
        #     self, Integrate._operator_, index, integrand,
        #     domain=domain, condition=condition, conditions=conditions,
        #     styles=styles)
        # new 20220111

        # If domain expressed as a special number set,
        # re-express domain as a continuous interval before
        # feeding as argument to OperationOverInstances.__init__().
        # if domain == Real:
        #     domain = IntervalOO(Neg(infinity), infinity)
        # elif domain == RealPos:
        #     domain = IntervalOO(zero, infinity)
        # elif domain == RealNonNeg:
        #     domain = IntervalCO(zero, infinity)
        # elif domain == RealNeg:
        #     domain = IntervalOO(Neg(infinity), zero)
        # elif domain == RealNonPos:
        #     domain = IntervalOC(Neg(infinity), zero)

        OperationOverInstances.__init__(
            self, Integrate._operator_, index_or_indices, integrand,
            domain=domain, domains=domains, condition=condition,
            conditions=conditions, styles=styles, _lambda_map=_lambda_map)
        # original
        # if len(self.instance_vars) != 1:
        #     raise ValueError('Only one index allowed per integral!')
        # elif isinstance(self.domain, Interval):
        #     raise ValueError('Can\'t integrate over DiscreteContiguousSet!')
        # elif self.domain == Real:
        #     self.domain = IntervalCC(Neg(infinity), infinity)
        # self.index = self.instance_vars[0]
        # self.integrand = self.instance_expr
        # new
        if hasattr(self, 'instance_param'):
            self.index = self.instance_param
        if hasattr(self, 'instance_params'):
            self.indices = self.instance_params
            if len(self.instance_params.entries) != 1:
                raise ValueError('Only one index allowed per integral!')
        if isinstance(self.domain, Interval):
            # elaborate this error message later
            raise ValueError('Can\'t integrate over DiscreteContiguousSet!')
        self.integrand = self.instance_expr

    def _closureTheorem(self, number_set):
        from . import theorems
        #import complex.theorems
        if number_set == Real:
            return theorems.integration_closure
        # if number_set == Complex:
        #    return complex.theorems.integration_closure

    # borrowed from / based on / Sum.deduce_in_number_set()
    # delete this comment after testing
    @relation_prover
    def deduce_in_number_set(self, number_set, **defaults_config):
        from . import (integration_real_neg_closure,
                       integration_real_non_pos_closure,
                       integration_real_non_neg_closure,
                       integration_real_pos_closure,
                       integration_real_closure)

        _x_sub = self.instance_params
        _f_sub = Lambda(_x_sub, self.instance_expr)
        _S_sub = self.domain
        _n_sub = _x_sub.num_elements()

        if number_set == RealNeg:
            thm = integration_real_neg_closure
        elif number_set == RealNonPos:
            thm = integration_real_non_pos_closure
        elif number_set == RealNonNeg:
            thm = integration_real_non_neg_closure
        elif number_set == RealPos:
            thm = integration_real_pos_closure
        elif number_set == Real:
            thm = integration_real_closure
        else:
            raise NotImplementedError(
                "'Integrate.deduce_in_number_set()' not implemented "
                "for the set {}".format(number_set))
        from proveit import n, x, f, S
        # Setting auto_simplify=True because the conjunction in the
        # integrate conditions needs to be simplified; there is no
        # danger of oversimplification since 'self' will be preserved
        # and domain is just the number set.
        impl = thm.instantiate(
            { n: _n_sub, x: _x_sub, f: _f_sub, S: _S_sub}, auto_simplify=True)
        antecedent = impl.antecedent
        # probably already doing this automatically now:
        # if not antecedent.proven():
        #     # Conclude the antecedent via generalization.
        #     antecedent.conclude_via_generalization()
        return impl.derive_consequent()

#     def formatted(self, format_type, fence=False):
#         # if isinstance(self.domain,IntervalOO) or
#         # isinstance(self.domain,IntervalOC) or
#         # isinstance(self.domain,IntervalCO) or
#         # isinstance(self.domain,IntervalOO):
#         if isinstance(self.domain, IntervalCC):
#             lower = self.domain.lower_bound.formatted(format_type)
#             upper = self.domain.upper_bound.formatted(format_type)
#             return self.operator.formatted(format_type) + r'_{' + lower + r'}' + r'^{' + upper + r'}' + self.integrand.formatted(
#                 format_type, fence=fence) + 'd' + self.index.formatted(format_type)
# #        elif self.domain

#         return self.operator.formatted(format_type) + r'_{' + self.domain.formatted(
#             format_type) + r'}' + self.integrand.formatted(format_type, fence=fence) + 'd' + self.index.formatted(format_type)

    def _formatted(self, format_type, **kwargs):
        # ACTUALLY, notice that the open-interval versions
        # probably lead to incorrect upper/lower bounds on the
        # formatted integrals. For example, an integral over the
        # open half-open interval (0, 1] would need to be formatted
        # or expressed as a limit as 'a' approaches 0 from the right
        # of the integral from 0 to 1.
        fence = kwargs['fence'] if 'fence' in kwargs else False
        if (isinstance(self.domain,IntervalCC) or
            isinstance(self.domain,IntervalCO) or
            isinstance(self.domain,IntervalOC) or
            isinstance(self.domain,IntervalOO)):

            lower = self.domain.lower_bound.formatted(format_type)
            upper = self.domain.upper_bound.formatted(format_type)
            formatted_inner = (
                    self.operator.formatted(format_type) +
                    r'_{' + lower + r'}' + r'^{' + upper + r'} ')
            explicit_ivars = list(self.explicit_instance_vars())
            has_explicit_ivars = (len(explicit_ivars) > 0)
            explicit_conds = list(self.explicit_conditions())
            has_explicit_conds = (len(explicit_conds) > 0)
            if has_explicit_conds:
                if has_explicit_ivars:
                    formatted_inner += " | "
                formatted_inner += ', '.join(condition.formatted(format_type)
                                             for condition in explicit_conds)
            formatted_inner += (
                    self.integrand.formatted(format_type, fence=fence) +
                    r'\,d' + self.index.formatted(format_type))

            # old/previous
            # return (self.operator.formatted(format_type) +
            #         r'_{' + lower + r'}' + r'^{' + upper + r'}' +
            #         self.integrand.formatted(format_type, fence=fence) +
            #         'd' + self.index.formatted(format_type))
            
            return maybe_fenced(format_type, formatted_inner, fence=fence)
        else:
            return OperationOverInstances._formatted(self, format_type,
                                                     fence=fence)
