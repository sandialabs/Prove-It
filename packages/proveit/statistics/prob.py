from proveit import Function, Operation, Literal, relation_prover
from proveit import x, X, Omega

pkg = __package__


class Prob(Function):
    '''
    Represents the probability of a sample in a sample space or
    an event, a set of samples in a sample space.
    '''
    # the literal operator of the Prob operation class
    _operator_ = Literal('Pr', latex_format=r'\textrm{Pr}', theory=__file__)

    def __init__(self, event, *, styles=None):
        Function.__init__(self, Prob._operator_, event, styles=styles)
        self.event = self.operand
    
    @relation_prover
    def deduce_in_prob_domain(self, sample_space, is_event=None,
                              **defaults_config):
        '''
        Prove that this Prob is between 0 and 1 given that its
        operand is in a sample space or a subset of the sample space.
        Set is_event to true/false to indicate that this is/isn't a 
        probability of an event.  If left as None, this is inferred.
        '''
        from . import prob_in_interval, event_prob_in_interval
        from proveit.logic import InSet, SubsetEq
        from proveit.logic.sets import (
                Set, Union, Intersect, Difference, SetOfAll,
                PowerSet, CartProd, CartExp)
        if is_event==False or InSet(self.operand, sample_space).proven():
            # This is a sample probability.
            return prob_in_interval.instantiate(
                    {Omega:sample_space, x:self.operand})
        if is_event==True or SubsetEq(self.operand, sample_space).proven():
            # This is an event probability.
            return event_prob_in_interval.instantiate(
                    {Omega:sample_space, X:self.operand})
        for set_expr in (Set, Union, Intersect, Difference, SetOfAll,
                         PowerSet, CartProd, CartExp):
            if isinstance(self.operand, set_expr):
                # Infer this is an event probability because the
                # operand is a set-type expression.
                return event_prob_in_interval.instantiate(
                        {Omega:sample_space, X:self.operand})
        # Assume this is a sample probability because there is
        # no indication to the contrary.
        return prob_in_interval.instantiate(
                {Omega:sample_space, x:self.operand})

