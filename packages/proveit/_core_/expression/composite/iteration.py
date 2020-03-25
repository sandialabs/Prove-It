from proveit._core_.expression.expr import (Expression, MakeNotImplemented,
                                            ImproperSubstitution)
from proveit._core_.expression.lambda_expr.lambda_expr import Lambda
from proveit._core_.expression.composite import Composite, ExprTuple, singleOrCompositeExpression, compositeExpression
from proveit._core_.expression.conditional import Conditional
from proveit._core_.defaults import defaults, USE_DEFAULTS
import itertools

class Iter(Expression):
    '''
    An Iter expression represents an iteration of "element" expressions
    within a containing ExprTuple.  It represents this as a Lambda to map
    each valid index value to a corresponding element, along with a
    start and end index value.  The represented element sequence corresponds
    to index values going from the start to the end in increments of 1.
    
    For example,
    1/i + ... + 1/j
    is internall represented by an Add operation with the following as its
    "operands":
    (1/i, ..., 1/j).
    These "operands" are represented by an ExprTuple with a single "entry"
    which is an Iter whose `lambda_map` is "k |-> 1/k", `start_index` is "i",
    and `end_index` is "j".  An ExprTuple "entry" may generally either be
    a singuler element or an Iter that represents multiple elements.
    '''

    def __init__(self, parameter, body, start_index, end_index, _lambda_map=None):
        '''
        Create an Iter that represents an iteration of the body for the
        parameter ranging from the start index to the end index.  
        A Lambda expression will be created as its 
        sub-expression that maps the parameter(s) to the body with
        conditions that restrict the parameter(s) to the appropriate interval.
        
        _lambda_map is used internally for efficiently rebuilding an Iter.
        '''
        from proveit.logic import InSet
        from proveit.number import Interval
        
        if _lambda_map is not None:
            # Use the provided 'lambda_map' instead of creating one.
            lambda_map = _lambda_map
            pos_args = (parameter, body, start_index, end_index)
            if pos_args != (None, None, None, None):
                raise ValueError("Positional arguments of the Init constructor "
                                 "should be None if lambda_map is provided.")
            parameter = lambda_map.parameter
            condition = lambda_map.body.condition
            invalid_condition_msg = ("Not the right kind of lambda_map condition "
                                     "for an iteration")
            if not isinstance(condition, InSet) or condition.element != parameter:
                raise ValueError(invalid_condition_msg)
            domain = condition.domain
            if not isinstance(domain, Interval):
                raise ValueError(invalid_condition_msg)
            self.start_index, self.end_index = domain.lowerBound, domain.upperBound
        else:
            self.start_index = start_index
            self.end_index = end_index
            condition = InSet(parameter, Interval(start_index, end_index))
            conditional = Conditional(body, condition)
            lambda_map = Lambda(parameter, conditional)
        
        Expression.__init__(self, ['Iter'], [lambda_map])
        self.lambda_map = lambda_map
        # The body of the Lambda map is a Conditional that conditions the 
        # mapping according to the parameter being in the [start, end] 
        # interval.  We'll use self.body to refer to the value of this
        # conditional.
        self.parameter = self.lambda_map.parameter
        self.body = self.lambda_map.body.value
    
    @classmethod
    def _make(subClass, coreInfo, styles, subExpressions):
        if subClass != Iter: 
            MakeNotImplemented(subClass)
        if len(coreInfo) != 1 or coreInfo[0] != 'Iter':
            raise ValueError("Expecting Iter coreInfo to contain exactly one item: 'Iter'")
        lambda_map = subExpressions[0]
        return Iter(None, None, None, None, _lambda_map=lambda_map).withStyles(**styles)
            
    def remakeArguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Iter.
        '''
        yield self.lambda_map.parameter
        yield self.lambda_map.body
        yield self.start_index
        yield self.end_index
        
    def first(self):
        '''
        Return the first instance of the iteration (and store for future use).
        '''
        if not hasattr(self, '_first'):
            expr_map = {self.lambda_map.parameter:self.start_index}
            self._first =  self.body.substituted(expr_map)
        return self._first

    def last(self):
        '''
        Return the last instance of the iteration (and store for futurle use).
        '''
        if not hasattr(self, '_last'):
            expr_map = {self.lambda_map.parameter:self.end_index}
            self._last = self.body.substituted(expr_map)
        return self._last
    
        
    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)
        
    def formatted(self, formatType, fence=False, subFence=True, operator=None, **kwargs):
        if operator is None:
            formatted_operator = ',' # comma is the default formatted operator
        elif isinstance(operator, str):
            formatted_operator = operator
        else:
            formatted_operator = operator.formatted(formatType)
        formatted_sub_expressions = [subExpr.formatted(formatType, fence=subFence) for subExpr in (self.first(), self.last())]
        formatted_sub_expressions.insert(1, '\ldots' if formatType=='latex' else '...')
        # Normally the iteration will be wrapped in an ExprTuple and fencing
        # will be handled externally.  When it isn't, we don't want to fence it
        # anyway.
        return formatted_operator.join(formatted_sub_expressions)
    
    def getInstance(self, index, assumptions = USE_DEFAULTS, requirements = None):
        '''
        Return the iteration instance with the given index
        as an Expression, using the given assumptions as needed
        to interpret the indices expression.  Required
        truths, proven under the given assumptions, that 
        were used to make this interpretation will be
        appended to the given 'requirements' (if provided).
        '''
        from proveit.number import LessEq
        
        if requirements is None:
            # requirements won't be passed back in this case 
            requirements = [] 
        
        # first make sure that the indices are in the iteration range
        start, end = self.start_index, self.end_index
        for first, second in ((start, index), (index, end)):
            relation = None
            try:
                relation = LessEq.sort([first, second], reorder=False, 
                                       assumptions=assumptions)
            except:
                raise IterationError("Indices not provably within the iteration "
                                     "range: %s <= %s"%(first, second)) 
            requirements.append(relation)
        
        # map to the desired instance
        return self.lambda_map.apply(index)
    
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
        See the Operation.substituted and Lambda.apply documentation for more 
        details.
        
        There are limitations with respect to applying a Lambda map with
        iterated parameters that are enforced here in Iter.substituted.
        
        First, iterated parameter variables must only be contained in 
        an IndexedVar with indices iterated over the same range (same start 
        and end index) as the parameter iteration itself.  
        The following example meets this restriction.
        
        Applying the Lambda
        (x, y_1, ..., y_3, z_i, ..., z_j) -> 
            x*y_1 + ... + x*y_3 + z_i + ... + z_j
        to operands (a, b, c, d, e_m, ..., e_n, f)
        will result in a*b + a*c + a*d + e_m + ... _ e_n + f provided that
        |(b, c, d)| = |(1, ..., 3)| is proven in advance and that
        |(e_m, ..., e_n, f)| = |(i, ..., j)| can be proven via automation.            
        
        A counter-example not meeting the restriction is
        (x_1, ..., x_n) -> x_1 * ... * x_j
        since the 'n' and 'j' do not match.
        
        Second, all expanded indexed variables within an Iter must
        have matching expansions in that corresponding entries must
        mutually be singular or iterations and iteration ranges
        must match.  For example,
        (x_1, ..., x_n, y_1, ..., y_n) -> x_1*y_1 + ... + x_n*y_n
        may be applied to
        (a_1, ..., a_{n-1}, b, c_1, ..., c_{n-1}, d)
        to produce 
        a_1*c_1 + ... + a_{n-1}*c_{n-1} + b*d
        but may not be applied to
        (a, b_1, ..., b_{n-1}, c_1, ..., c_{n-1}, d)
        
        In order to handle these restricted cases, transformations must be
        made to bring the IndexedVar iteration in alignment.   Use methods such
        as Lambda.relabeled, Iteration.partition, or Iteration.split to do 
        this.
        
        See the Lambda.apply documentation for a related discussion.
        '''
        from proveit.logic import Equals, InSet
        from proveit.number import Interval

        if len(repl_map)>0 and (self in repl_map):
            # The full expression is to be substituted.
            return repl_map[self]._restrictionChecked(reserved_vars)
        
        assumptions = defaults.checkedAssumptions(assumptions)
        new_requirements = []
        lambda_map = self.lambda_map
        parameter = self.parameter
        
        # Check if any of the IndexedVars whose index is the iteration
        # parameter is being expanded by the repl_map.
        must_expand = False
        first_expanded_indexed_var = None
        indexed_vars_of_iter = self.lambda_map.freeIndexedVars(self.parameter)
        for indexed_var in indexed_vars_of_iter:
            if indexed_var.var in repl_map \
                    and isinstance(repl_map[indexed_var.var], ExprTuple):
                first_expanded_var = indexed_var.var
                must_expand = True
        
        if not must_expand:
            # No need to worry about expanding IndexedVar's.  Just call
            # 'substituted' on the Lambda map sub-expression.
            subbed_lambda_map = lambda_map.substituted(repl_map, reserved_vars, 
                                                       assumptions, requirements)
            yield Iter(None, None, None, None, _lambda_map = subbed_lambda_map)
            return True
        
        # Need to expand IndexedVar's.  The expansions must be defined over
        # the range of this iteration and must be aligned with each other.
        
        # The repl_map should map each variable being indexed to the same
        # range of indices covered by this Iter to keep track that we
        # have the correct range.
        for indexed_var in indexed_vars_of_iter:
            # indexed_var_iter_tuple should be something like (x_i, ..., x_j)
            # where i and j match the start and end indices of this Iter.
            indexed_var_iter_tuple = repl_map[indexed_var.var]
            if len(indexed_var_iter_tuple) != 1:
                raise error
            indexed_var_iter = indexed_var_iter_tuple[0]
            if not isinstance(indexed_var_iter, Iter):
                raise error
            if indexed_var_iter.start_index != self.start_index:
                raise error
            if indexed_var_iter.end_index != self.end_index:
                raise error
        
        def raise_failed_to_expand(first_expanded_indexed_var, indexed_var):
            raise ImproperSubstitution("When expanding IndexedVar's within an"
                                       "Iter whose parameter is the index, they"
                                       "must all be expanded together.  "
                                       "%s is being expanded but %s is not"
                                       %(first_expanded_indexed_var, indexed_var))
        def raise_failed_match(first_expansion, expansion):
            raise ImproperSubstitution("When expanding IndexedVar's within an"
                                       "Iter whose parameter is the index, their"
                                       "expansion Iter indices must all match,
                                       "unlike %s vs %s."
                                       %(first_expansion, expansion))
        
        first_indexed_var_iter_tuple = repl_map[first_expanded_var]
        first_expansion = repl_map.get(first_indexed_var_iter_tuple, 
                                       first_indexed_var_iter_tuple)


        # Need to handle the change in scope within the lambda 
        # expression.  We won't use 'new_params'.  They aren't relavent 
        # after an expansion, this won't be used.
        new_params, inner_repl_map, inner_assumptions, inner_reserved_vars \
            = self.lambda_map._innerScopeSub(repl_map, reserved_vars, 
                                             assumptions, new_requirements)
        assert len(new_params)==1
        new_param = new_params[0]
        
        # Loop over the entries of the first expansion which must be
        # in correspondence (same Iter range or the same in being singular)
        # with the other expansions.
        for k, first_expansion_entry in enumerate(first_expansion):
            entry_repl_map = dict(inner_repl_map)       
            # Loop over all of the IndexedVar's being expanded and make
            # sure their kth entry is in correspondence with the first
            # expansions kth entry (with respect to Iter range or being
            # singular).
            for indexed_var in indexed_vars_of_iter:
                expansion = None
                if indexed_var.var in inner_repl_map:
                    indexed_var_iter_tuple = inner_repl_map[indexed_var.var]
                    expansion = inner_repl_map.get(indexed_var_iter_tuple, 
                                                   indexed_var_iter_tuple)
                    if not isinstance(expansion, ExprTupe): expansion=None
                if expansion is None:
                    # Failing to all expand together.
                    raise_failed_to_expand(first_expanded_indexed_var, indexed_var)
                if len(expansion) != len(first_expansion):
                    # Failing to have the same number of entries.
                    raise_failed_match(first_expansion, expansion)
                entry = expansion[k]
                if isinstance(entry, Iter) != isinstance(first_expansion_entry, Iter):
                    # Failing to match w.r.t. being singular or not.
                    raise_failed_match(first_expansion, expansion)
                if isinstance(entry, Iter):
                    if entry.start_index !=  first_expansion_entry.start_index:
                        # Failed to have the same Iter range (different start).
                        raise_failed_match(first_expansion, expansion)
                    if entry.entry_index !=  first_expansion_entry.entry_index:
                        # Failed to have the same Iter range (different end).
                        raise_failed_match(first_expansion, expansion)
                    # Relabel the entry body to use the parameter of this
                    # Iter so that all the parameters will be consistent.
                    new_body = entry.body.substituted({entry.parameter:parameter})
                    # For this entry, replace the IndexedVar with the 
                    # corresponding Iter body.
                    entry_repl_map[indexed_var] = new_body
                else:
                    # For this entry, replace the IndexedVar with the
                    # corresponding singular element.
                    entry_repl_map[indexed_var] = entry
            # Now yield the substitution corresponding to this entry.
            if isinstance(first_expansion_entry, Iter):
                # For an Iter entry, yield a new Iter using the entry_repl_map.
                start_index = first_expansion_entry.start_index
                end_index = first_expansion_entry.end_index
                range_assumption = InSet(parameter, Interval(start_index, end_index))
                entry_assumptions = inner_assumptions + [range_assumption]
                entry_requirements = []
                yield Iter(new_param,
                           body.substituted(entry_repl_map, inner_reserved_vars,
                                            entry_assumptions, entry_requirements),
                           start_index, end_index)
                # Translate from inner requirements to outer requirements
                # in a manner that respects the change in scope w.r.t.
                # lambda parameters.
                for requirement in entry_requirements:
                    if new_param in requirement.freeVars():
                        # If the requirement involves the Iter parameter,
                        # it must be generalized under these parameters to 
                        # ensure there is no scoping violation since this
                        # parameter's scope is within the new Iter.
                        conditions = requirement.assumptions
                        requirement = requirement.generalize(new_param,
                                                             conditions=conditions)
                    requirements.append(requirement)
            else:
                # For a singular element entry, yield the substituted element.
                yield body.substituted(entry_repl_map, inner_reserved_vars,
                                       inner_assumptions, requirements)
                
    
    def partition(self, before_split_idx, assumptions=USE_DEFAULTS):
        '''
        Return the equation between this iteration within an ExprTuple
        and a split version in the following manner: 
            (f(self.start_index), ..., f(self.end_index)) =
            (f(self.start_index), ..., f(before_split_index), 
             f(before_split_index+1), ..., f(self.end_index))
        where f represents the self.lambda_map.
        '''
        from proveit._common_ import f, i, j, k
        from proveit.logic import Equals
        from proveit.number import Add, one, subtract
        
        unconditioned_lambda = self.unconditionedMap()
        start_index, end_index = self.start_index, self.end_index
        if end_index == Add(before_split_idx, one):
            # special case which uses the axiom:
            from proveit.iteration._axioms_ import iterExtensionDef
            return iterExtensionDef.specialize(
                    {f:unconditioned_lambda, i:start_index, j:before_split_idx},
                    assumptions=assumptions)
        elif before_split_idx == self.start_index:
            # special case when pealing off the front
            from proveit.iteration._theorems_ import partition_front
            return partition_front.specialize(
                    {f:unconditioned_lambda, i:self.start_index, j:self.end_index},
                     assumptions=assumptions)
        elif (before_split_idx == subtract(end_index, one) or
              Equals(before_split_idx, subtract(end_index, one)).proven(assumptions)):
            # special case when pealing off the back
            from proveit.iteration._theorems_ import partition_back
            return partition_back.specialize(
                    {f:unconditioned_lambda, i:start_index, j:end_index},
                     assumptions=assumptions)
        else:
            from proveit.iteration._theorems_ import partition
            return partition.specialize(
                    {f:unconditioned_lambda, i:start_index, j:before_split_idx,
                     k:end_index}, assumptions=assumptions)
        
    
    """
    TODO: change register_equivalence_method to allow and fascilitate these
    method stubs for purposes of generating useful documentation.

    def partitioned(self, before_split_idx, assumptions=USE_DEFAULTS):
        '''
        Return the right-hand-side of a 'partition'.
        '''
        raise Exception("Should be implemented via InnerExpr.register_equivalence_method")
    
    def split(self, before_split_idx, assumptions=USE_DEFAULTS):
        '''
        As an InnerExpr method when the inner expression is an Iter,
        return the expression with the inner expression replaced by its
        'partitioned' version.
        '''
        raise Exception("Implemented via InnerExpr.register_equivalence_method "
                        "only to be applied to an InnerExpr object.")
    """


def varIter(var, start, end):
    from proveit import safeDummyVar, IndexedVar
    param = safeDummyVar(var)
    return Iter(param, IndexedVar(var, param), start, end)
