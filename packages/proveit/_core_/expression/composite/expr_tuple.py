from .composite import Composite, _simplifiedCoord
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.proof import ProofFailure
from proveit._core_.defaults import USE_DEFAULTS
from proveit._core_.expression.style_options import StyleOptions

class ExprTuple(Composite, Expression):
    """
    An ExprTuple is a composite Exporession composed of an ordered list 
    of member Expressions.
    """
    
    def __init__(self, *expressions, styles=None):
        '''
        Initialize an ExprTuple from an iterable over Expression 
        objects.  When subsequent iterations in the tuple form a
        self-evident continuation, these iterations will be joined.
        For example, (a_1, ..., a_n, a_{n+1}, ..., a_m) will join to
        form (a_1, ..., a_m).  "Self-evident" falls under two 
        categories: the start of the second iteration is the
        successor to the end of the first iteration (e.g., n and n+1)
        or the end of the first iteration is the predecessor of the
        start of the second iteration (e.g., n-1 and n).  To be a
        valid ExprTuple, all iterations must span a range whose
        extent is a natural number.  In the above example with the
        tuple of "a"-indexed iterations, n must be a natural number
        and m-n must be a natural number for the ExprTuple to be
        valid (note that iterations may have an extent of zero).
        When an ExprTuple is created, there is not a general check
        that it is valid.  However, when deriving new known truths
        from valid existing known truths, validity is guaranteed to
        be maintained (in particular, specializations that transform
        ExprTuples ensure that validity is maintained).  The joining
        of iterations is valid as long as the original iterations
        are valid, so this process is also one that maintains validity
        which is the thing that is important.
        '''
        from proveit._core_ import KnownTruth
        from .composite import singleOrCompositeExpression
        entries = []
        for entry in expressions:
            if isinstance(entry, KnownTruth):
                # Extract the Expression from the KnownTruth:
                entry = entry.expr 
            if not isinstance(entry, Expression):
                entry = singleOrCompositeExpression(entry)
            if not isinstance(entry, Expression):
                raise TypeError("ExprTuple must be created out of "
                                  "Expressions, not %s."%entry.__class__)
            entries.append(entry)
        self.entries = tuple(entries)
        self._lastEntryCoordInfo = None
        self._lastQueriedEntryIndex = 0
        
        if styles is None: styles = dict()
        if 'operation' not in styles:
            styles['operation'] = 'normal' # vs 'function
        if 'wrapPositions' not in styles:
            styles['wrapPositions'] = '()' # no wrapping by default
        if 'justification' not in styles:
            styles['justification'] = 'left'

        Expression.__init__(self, ['ExprTuple'], self.entries, styles=styles)

    def styleOptions(self):
        options = StyleOptions(self)
        options.addOption('wrapPositions', 
                          ("position(s) at which wrapping is to occur; 'n' "
                           "is after the nth comma."))
        options.addOption('justification', 
                          ("if any wrap positions are set, justify to the 'left', "
                           "'center', or 'right'"))
        return options

    def withWrappingAt(self, *wrapPositions):
        return self.withStyles(wrapPositions='(' + ' '.join(str(pos) for pos in wrapPositions) + ')')
    
    def withJustification(self, justification):
        return self.withStyles(justification=justification)
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != ExprTuple: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'ExprTuple':
            raise ValueError("Expecting ExprTuple coreInfo to contain "
                               "exactly one item: 'ExprTuple'")
        return ExprTuple(*subExpressions).withStyles(**styles)      

    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the ExprTuple.
        '''
        for subExpr in self.subExprIter():
            yield subExpr

    def remakeWithStyleCalls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a 
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'withWrappingAt'
        and 'withJustification' calls.
        '''
        wrap_positions = self.wrapPositions()
        call_strs = []
        if len(wrap_positions) > 0:
            call_strs.append('withWrappingAt(' + ','.join(str(pos) for pos in wrap_positions) + ')')
        justification = self.getStyle('justification')
        if justification != 'center':
            call_strs.append('withJustification(' + justification + ')')
        return call_strs
                                        
    def __iter__(self):
        '''
        Iterator over the entries of the list.
        Some entries may be iterations (Iter) that 
        represent multiple elements of the list.
        '''
        return iter(self.entries)
    
    def __len__(self):
        '''
        Return the number of entries of the list.
        Some entries may be iterations (Iter) that 
        represent multiple elements of the list.
        '''
        return len(self.entries)

    def __getitem__(self, i):
        '''
        Return the list entry at the ith index.
        This is a relative entry-wise index where
        entries may represent multiple elements
        via iterations (Iter).
        '''
        return self.entries[i]
    
    def __add__(self, other):
        '''
        Concatenate ExprTuple's together via '+' just like
        Python lists.  Actually works with any iterable
        of Expressions as the second argument.
        '''
        return ExprTuple(*(self.entries + tuple(other)))
    
    def singular(self):
        '''
        Return True if this has a single element that is not an
        iteration.
        '''
        from .expr_range import ExprRange
        return len(self)==1 and not isinstance(self[0], ExprRange)
    
    def index(self, entry, start=0, stop=None):
        if stop is None:
            return self.entries.index(entry, start)
        else:
            return self.entries.index(entry, start, stop)

    def wrapPositions(self):
        '''
        Return a list of wrap positions according to the current style setting.
        Position 'n' is after the nth comma.
        '''
        return [int(pos_str) for pos_str in self.getStyle('wrapPositions').strip('()').split(' ') if pos_str != '']
    
    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
        
    def formatted(self, formatType, fence=True, subFence=False, operatorOrOperators=None, implicitFirstOperator=False, 
                  wrapPositions=None, justification=None):
        from .expr_range import ExprRange

        outStr = ''
        if len(self) == 0 and fence: 
            # for an empty list, show the parenthesis to show something.            
            return '()'
        
        if wrapPositions is None:
            # Convert from a convention where position 'n' is after the nth comma to one in which the position '2n' is 
            # after the nth operator (which also allow for position before operators).
            wrapPositions = [2*pos for pos in self.wrapPositions()]
        if justification is None:
            justification = self.getStyle('justification', 'left')
        
        do_wrapping = len(wrapPositions)>0
        if fence: outStr = '(' if formatType=='string' else  r'\left('
        if do_wrapping and formatType=='latex': 
            outStr += r'\begin{array}{%s} '%justification[0]
        
        ellipses = r'\ldots' if formatType=='latex' else ' ... '
        formatted_sub_expressions = []
        for sub_expr in self:
            if isinstance(sub_expr, ExprRange):
                formatted_sub_expressions += [sub_expr.first().formatted(formatType, fence=subFence), ellipses, sub_expr.last().formatted(formatType, fence=subFence)]
            elif isinstance(sub_expr, ExprTuple):
                # always fence nested expression lists                
                formatted_sub_expressions.append(sub_expr.formatted(formatType, fence=True))
            else:
                formatted_sub_expressions.append(sub_expr.formatted(formatType, fence=subFence))
        
        # put the formatted operator between each of formattedSubExpressions
        for wrap_position in wrapPositions:
            if wrap_position%2==1:
                # wrap after operand (before next operation)
                formatted_sub_expressions[(wrap_position-1)//2] += r' \\ '
            else:
                # wrap after operation (before next operand)
                formatted_sub_expressions[wrap_position//2] = r' \\ ' + formatted_sub_expressions[wrap_position//2]
        if operatorOrOperators is None:
            operatorOrOperators = ','
        elif isinstance(operatorOrOperators, Expression) and not isinstance(operatorOrOperators, ExprTuple):
            operatorOrOperators = operatorOrOperators.formatted(formatType)
        if isinstance(operatorOrOperators, str):
            # single operator
            formatted_operator = operatorOrOperators
            outStr += (' '+formatted_operator+' ').join(formatted_sub_expressions)
        else:
            # assume all different operators
            formatted_operators = []
            for operator in operatorOrOperators:
                if isinstance(operator, ExprRange):
                    formatted_operators += [operator.first().formatted(formatType), '', operator.last().formatted(formatType)]
                else:
                    formatted_operators.append(operator.formatted(formatType))
            if len(formatted_sub_expressions) == len(formatted_operators):
                # operator preceeds each operand
                if implicitFirstOperator:
                    outStr = formatted_sub_expressions[0] # first operator is implicit
                else:
                    outStr = formatted_operators[0] + formatted_sub_expressions[0] # no space after first operator
                outStr += ' ' # space before next operator
                outStr += ' '.join(formatted_operator + ' ' + formatted_operand for formatted_operator, formatted_operand in zip(formatted_operators[1:], formatted_sub_expressions[1:]))
            elif len(formatted_sub_expressions) == len(formatted_operators)+1:
                # operator between each operand
                outStr = ' '.join(formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in zip(formatted_sub_expressions, formatted_operators))
                outStr += ' ' + formatted_sub_expressions[-1]
            elif len(formatted_sub_expressions) != len(formatted_operators):
                raise ValueError("May only perform ExprTuple formatting if the number of operators is equal to the number of operands (precedes each operand) or one less (between each operand); also, operator iterations must be in correpsondence with operand iterations.")

        if do_wrapping and formatType=='latex': 
            outStr += r' \end{array}'
        if fence: outStr += ')' if formatType=='string' else  r'\right)'
        
        return outStr
    
    def length(self, assumptions=USE_DEFAULTS):
        '''
        Return the proven length of this tuple as an Expression.  This
        length includes the extent of all contained iterations. 
        '''
        from proveit import Len
        return Len(self).simplification(assumptions).rhs
                
    def substituted(self, repl_map, reserved_vars=None, 
                    assumptions=USE_DEFAULTS, requirements=None):
        '''
        Returns this expression with sub-expressions substituted 
        according to the replacement map (repl_map) dictionary.
        
        reserved_vars is used internally to protect the "scope" of a
        Lambda map.  For more details, see the Lambda.substitution
        documentation.

        'assumptions' and 'requirements' are used when an operator is
        substituted by a Lambda map that has iterated parameters such that 
        the length of the parameters and operands must be proven to be equal.
        For more details, see Operation.substituted, Lambda.apply, and
        Iter.substituted (which is the sequence of calls involved).
        
        For an ExprTuple, each entry is 'substituted' independently.  For an
        entry that is an Iter, its results are embedded as one or more entries 
        of the ExprTuple.
        '''
        from .expr_range import ExprRange
        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]._restrictionChecked(reserved_vars)
        
        subbed_exprs = []
        for expr in self:
            if isinstance(expr, ExprRange):
                # ExprRange.substituted is a generator that yields items to be
                # embedded into the tuple.
                for subbed_item in expr.substituted(repl_map, reserved_vars, 
                                                    assumptions, requirements):
                    subbed_exprs.append(subbed_item)
            else:
                subbed_expr = expr.substituted(repl_map, reserved_vars, 
                                               assumptions, requirements)
                subbed_exprs.append(subbed_expr)
        return ExprTuple(*subbed_exprs)
    
    def merger(self, assumptions=USE_DEFAULTS):
        '''
        If this is an tuple of expressions that can be directly merged 
        together into a single ExprRange, return this proven 
        equivalence.  For example,
        {j \in Naturals, k-(j+1) \in Naturals} 
        |- (x_1, .., x_j, x_{j+1}, x_{j+2}, ..., x_k) = (x_1, ..., x_k)
        '''
        from proveit._core_.expression.lambda_expr import Lambda
        from .expr_range import ExprRange
        from proveit.relation import TransRelUpdater
        from proveit.iteration._theorems_ import (merge, merge_front, merge_back,
                                                  merge_pair, merge_series)
        from proveit._common_ import f, i, j, k, l, x
        
        # A convenience to allow successive update to the equation via 
        # transitivities (starting with self=self).
        eq = TransRelUpdater(self, assumptions)
        
        # Determine the position of the first Iter item and get the lambda map.
        first_iter_pos = len(self)
        lambda_map = None
        for _k, item in enumerate(self):
            if isinstance(item, ExprRange):
                lambda_map = Lambda(item.lambda_map.parameter, item.lambda_map.body)
                first_iter_pos = _k
                break
        
        if 1 < first_iter_pos:
            if lambda_map is None:
                raise NotImplementedError("Means of extracting a lambda map has not been implemented")
                pass # need the lambda map
            # Collapse singular items at the beginning.
            front_singles = ExprTuple(eq.expr[:first_iter_pos])
            i_sub = lambda_map.extractArgument(front_singles[0])
            j_sub = lambda_map.extractArgument(front_singles[-1])
            if len(front_singles)==2:
                # Merge a pair of singular items.
                front_merger = merge_pair.specialize({f:lambda_map, i:i_sub, j:j_sub}, 
                                                     assumptions=assumptions)
            else:
                # Merge a series of singular items in one shot.
                front_merger = merge_series.specialize({f:lambda_map, x:front_singles,
                                                        i:i_sub, j:j_sub}, 
                                                       assumptions=assumptions)
            eq.update(front_merger.substitution(self.innerExpr()[:first_iter_pos], 
                                                assumptions=assumptions))
            
        if len(eq.expr) == 1:
            # We have accomplished a merger down to one item.
            return eq.relation
        
        if len(eq.expr) == 2:
            # Merge a pair.
            if isinstance(eq.expr[0], Iter):
                if isinstance(eq.expr[1], Iter):
                    # Merge a pair of Iters.
                    item = eq.expr[1]
                    other_lambda_map = Lambda(item.lambda_map.parameter, 
                                              item.lambda_map.body)
                    if other_lambda_map != lambda_map:
                        raise ExprTupleError("Cannot merge together iterations "
                                             "with different lambda maps: %s vs %s"
                                             %(lambda_map, other_lambda_map))
                    iSub, jSub = eq.expr[0].start_index, eq.expr[0].end_index
                    kSub, lSub = eq.expr[1].start_index, eq.expr[1].end_index
                    merger = \
                        merge.specialize({f:lambda_map, i:iSub, j:jSub, k:kSub, 
                                          l:lSub}, assumptions=assumptions)
                else:
                    # Merge an Iter and a singular item.
                    iSub, jSub = eq.expr[0].start_index, eq.expr[0].end_index
                    kSub = lambda_map.extractArgument(eq.expr[1])
                    merger = \
                        merge_back.specialize({f:lambda_map, i:iSub, j:jSub,
                                               k:kSub}, assumptions=assumptions)                    
            else:
                # Merge a singular item and Iter.
                iSub = lambda_map.extractArgument(eq.expr[0])
                jSub, kSub = eq.expr[1].start_index, eq.expr[1].end_index
                merger = \
                    merge_front.specialize({f:lambda_map, i:iSub, j:jSub,
                                            k:kSub}, assumptions=assumptions)
            eq.update(merger)
            return eq.relation
        
        while len(eq.expr) > 1:
            front_merger = ExprTuple(eq.expr[:2]).merger(assumptions)
            eq.update(front_merger.substitution(self.innerExpr()[:2], 
                                                assumptions=assumptions))
    
    """
    TODO: change register_equivalence_method to allow and fascilitate these
    method stubs for purposes of generating useful documentation.
    
    def merged(self, assumptions=USE_DEFAULTS):
        '''
        Return the right-hand-side of a 'merger'.
        '''
        raise Exception("Should be implemented via InnerExpr.register_equivalence_method")
    
    def merge(self, assumptions=USE_DEFAULTS):
        '''
        As an InnerExpr method when the inner expression is an ExprTuple,
        return the expression with the inner expression replaced by its
        'merged' version.
        '''
        raise Exception("Implemented via InnerExpr.register_equivalence_method "
                        "only to be applied to an InnerExpr object.")
    """


class ExprTupleError(Exception):
    def __init__(self, msg):
        self.msg = msg
    def __str__(self):
        return self.msg

class ConvertToMapError(Exception):
    def __init__(self, extra_msg):
        self.extra_msg = extra_msg
    def __str__(self):
        return ("The indices must be in correspondence with ExprTuple items "
                "when performing ExprTuple.convert_to_map: %s"%self.extr_msg)