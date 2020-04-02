from proveit import Operation, Literal, Iter, defaults, USE_DEFAULTS
from proveit._common_ import a, b, c, d, e, f, g, h, i, j, k, x, y, aa

class Len(Operation):
    # operator of the Length operation.
    _operator_ = Literal(stringFormat='length', context=__file__)   
    
    def __init__(self, operand):
        Operation.__init__(self, Len._operator_, operand)
        if not hasattr(self, 'operand'):
            self.operand = self.operands # always only one tuple operand
            if defaults.automation==True:
                # Handle some automation for dealing with
                # ExprTuple length requirements in the expansion of 
                # iterated parameters (see Lambda.apply).
                try:
                    self.autoInvocations()                            
                finally:
                    defaults.automation = True
    
    def autoInvocations(self):
        '''
        Invoke useful axioms/theorems pertaining to this Len expression
        for automation purposes.  In particular, these are meant for
        dealing with ExprTuple length requirements in the expansion of 
        iterated parameters (see Lambda.apply).
        '''
        # Avoid infinite recursion:
        defaults.automation = False 
        if len(self.operands)==1 and isinstance(self.operands[0], Iter):
            # In the special case of needing the length of an
            # iteration of the form (1, ..., n) where n is a decimal,
            # import theorems that may be relevant.  For example:
            # (1, 2, 3) = (1, ..., 3)
            # |(1, 2, 3)| = |(1, ..., 3)|
            from proveit.number import one
            import proveit.number.numeral.deci
            from proveit.number.numeral.deci import DIGITS
            iter_operand = self.operands[0]
            if iter_operand.body == iter_operand.parameter:
                start_index = iter_operand.start_index
                end_index = iter_operand.end_index
                if (start_index == one and end_index in DIGITS):
                    n = end_index.asInt()
                    proveit.number.numeral.deci._theorems_\
                        .__getattr__('count%d_iter'%n)
                    proveit.number.numeral.deci._theorems_\
                        .__getattr__('count%d_iter_len'%n)
        elif not any(isinstance(operand, Iter) for operand in self.operands):
            if 0 < len(self.operands) < 10:
                # Automatically get the count and equivalence with
                # the length of the proper iteration starting from
                # 1.  For example,
                # |(a, b, c)| = 3
                # |(a, b, c)| = |(1, .., 3)|
                import proveit.number.numeral.deci
                n = len(self.operands)
                len_thm = proveit.number.numeral.deci._theorems_\
                            .__getattr__('tuple%d_len'%n)
                iter_len_thm = proveit.number.numeral.deci._theorems_\
                                .__getattr__('tuple%d_iter_len'%n)
                repl_map = dict()
                for param, operand in zip(len_thm.explicitInstanceParams(),
                                          self.operands):
                    repl_map[param] = operand
                len_thm.specialize(repl_map)
                iter_len_thm.specialize(repl_map)        
        
    
    @staticmethod
    def extractInitArgValue(argName, operator_or_operators, operand_or_operands):
        if argName=='operand':
            return operand_or_operands
        
    def string(self, **kwargs):
        return '|' + self.operand.string() + '|'
    
    def latex(self, **kwargs):
        return '|' + self.operand.latex() + '|'
    
    def _computation(self, must_evaluate=False, assumptions=USE_DEFAULTS):
        '''
        Return the proven equivalence between this Len expression and its
        computed value which may or may not be an irreducible value.  If
        must_evaluate is True, then it must compute an irreducible value or
        raise a SimplificationError.
        '''
        from proveit import ExprTuple, Iter
        from proveit.iteration._axioms_ import tupleLen0
        from proveit.iteration._theorems_ import (singleElemLen, iterLen,
                                                  concatElemLen, concatIterLen, 
                                                  concatSimpleIterLen)
        from proveit.number.numeral.deci._theorems_ import tupleLen1, tupleLen2, tupleLen3, tupleLen4, tupleLen5
        from proveit.number.numeral.deci._theorems_ import tupleLen6, tupleLen7, tupleLen8, tupleLen9
        from proveit.number import one
        
        if len(self.operands) == 0:
            return tupleLen0
        
        has_iter = False
        for operand in self.operands:
            if isinstance(operand, Iter):
                has_iter = True
        
        if not has_iter and len(self.operands) < 10:
            if len(self.operands) == 0:
                return tupleLen0
            elif len(self.operands) == 1:
                return tupleLen1.specialize({a:self.operands[0]})
            elif len(self.operands) == 2:
                a_, b_ = self.operands
                return tupleLen2.specialize({a:a_, b:b_})
            elif len(self.operands) == 3:
                a_, b_, c_ = self.operands
                return tupleLen3.specialize({a:a_, b:b_, c:c_})
            elif len(self.operands) == 4:
                a_, b_, c_, d_ = self.operands
                return tupleLen4.specialize({a:a_, b:b_, c:c_, d:d_})
            elif len(self.operands) == 5:
                a_, b_, c_, d_, e_ = self.operands
                return tupleLen5.specialize({a:a_, b:b_, c:c_, d:d_, e:e_})
            elif len(self.operands) == 6:
                a_, b_, c_, d_, e_, f_ = self.operands
                return tupleLen6.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_})
            elif len(self.operands) == 7:
                a_, b_, c_, d_, e_, f_, g_ = self.operands
                return tupleLen7.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_,
                                             g:g_})
            elif len(self.operands) == 8:
                a_, b_, c_, d_, e_, f_, g_, h_ = self.operands
                return tupleLen8.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_, 
                                             g:g_, h:h_})
            elif len(self.operands) == 9:
                a_, b_, c_, d_, e_, f_, g_, h_, i_ = self.operands
                return tupleLen9.specialize({a:a_, b:b_, c:c_, d:d_, e:e_, f:f_, 
                                             g:g_, h:h_, i:i_})
        else:
            items = self.operands
            last_item_is_iter = isinstance(items[-1], Iter)
            if len(items) > 1: # Multiple items in the ExprTuple
                _a = ExprTuple(*items[:-1]) # leave off the end
                _i = _a.length(assumptions) # Obtain length of the first part.
                if last_item_is_iter:
                    # Multiple items with the last one being an Iter.
                    _f = items[-1].unconditionedMap()
                    if items[-1].start_index == one:
                        _j = items[-1].end_index
                        valuation = \
                            concatSimpleIterLen.specialize({i:_i, j:_j, aa:_a, f:_f},
                                                           assumptions=assumptions)
                    else:
                        _j = items[-1].start_index
                        _k = items[-1].end_index
                        valuation = \
                            concatIterLen.specialize({i:_i, j:_j, k:_k, aa:_a, f:_f},
                                                     assumptions=assumptions)
                else:
                    # Multiple items with the last one being a singular element.
                    valuation = concatElemLen.specialize({i:_i, aa:_a, b:items[-1]})
            elif last_item_is_iter:
                # A single iteration item.
                _f = items[-1].unconditionedMap()
                _i = items[-1].start_index
                _j = items[-1].end_index
                valuation = iterLen.specialize({f:_f, i:_i, j:_j}, 
                                               assumptions=assumptions)
            else:
                # Just a singular element.
                valuation = singleElemLen.specialize({a:items[0]}, 
                                                      assumptions=assumptions)
        
        if must_evaluate:
            rhs_simplification = valuation.rhs.evaluation(assumptions)
        else:
            rhs_simplification = valuation.rhs.simplification(assumptions)
        return valuation.applyTransitivity(rhs_simplification, assumptions)

    def doReducedSimplification(self, assumptions=USE_DEFAULTS):
        '''
        A simplification of a Len operation computes the length as a sum
        of the lengths of each item of the ExprTuple operand, returning
        the equivalence between the Len expression and this computation,
        simplified to the extent possible.  An item may be a singular element
        (contribution 1 to the length) or an iteration contributing its length.
        '''
        return self._computation(must_evaluate=False, assumptions=assumptions)
    
    def doReducedEvaluation(self, assumptions=USE_DEFAULTS):
        '''
        Return the evaluation of the length which equates that Len expression
        to an irreducible result.
        '''
        return self._computation(must_evaluate=True, assumptions=assumptions)
    
    def deduceInNaturalSet(assumptions=USE_DEFAULTS):
        pass
    
