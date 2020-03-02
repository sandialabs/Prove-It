from proveit import Context, Literal, Operation, USE_DEFAULTS

class Divides(Operation):
    
    # context = Context('.')
    # When I try to include latexFormat, I get an error
    # 'Implicit operator cannot be changed'
    _operator_ = Literal(
    	  stringFormat='|', latexFormat=r'\rvert', context=__file__
    	  )
    # _operator_ = Literal('|', context=__file__)
    
    def __init__(self, a, b):
        Operation.__init__(self, Divides._operator_, [a, b])

    def deduceInBool(self, assumptions=USE_DEFAULTS):
        '''
        Based on similar deduceInBool methods found in various classes in
        logic.booleans. Attempt to deduce, then return, that this 'Divides'
        expression is in the set of BOOLEANS.
        '''
        from ._axioms_ import dividesInBool
        from proveit._common_ import m, n
        return dividesInBool.specialize(
        	  {m:self.operands[0], n:self.operands[1]}, assumptions=assumptions)