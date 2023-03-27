from proveit._core_.expression.expr import (Expression, MakeNotImplemented,
                                            ImproperReplacement,
                                            free_vars, used_vars,
                                            traverse_inner_expressions)
from proveit._core_.expression.label.var import safe_dummy_var, safe_dummy_vars
from proveit._core_.expression.composite import is_single
from proveit._core_.defaults import defaults, USE_DEFAULTS
from proveit.decorators import prover, equality_prover
from collections import deque

def get_param_var(parameter, *, _required_indices=None):
    '''
    Parameters may be variables, indexed variables, ranges over indexed
    variables, or even nested ranges (ranges of ranges, etc) of indexed
    variables.  If it involves indexed variables, the "parameter
    variable" (that is introduced in the new scopse)
    is the variable being indexed.

    _required_indices is used for internal purposes to make sure
    unique indices are used in a range of variables.  For example,
    x_1, ..n repeats.., x_1
    should not be allowed.
    '''
    from proveit._core_.expression.label import Variable
    from proveit._core_.expression.composite import ExprRange
    from proveit._core_.expression.operation.indexed_var import IndexedVar
    if isinstance(parameter, ExprRange):
        # Only ExprRange parameters may be used as indices.
        if _required_indices is None:
            _required_indices = set()
        _required_indices.add(parameter.parameter)
        # recurse to get the parameter variable
        var = get_param_var(
            parameter.body,
            _required_indices=_required_indices)
        if len(_required_indices) > 0:
            raise ValueError(
                "Parameter may be an ExprRange over IndexedVar "
                "expressions (e.g., x_1, ..., x_n) or even nested "
                "ExprRanges (e.g., range of ranges of indexed "
                "variables), but each ExprRange parameter must appear "
                "as an index of the IndexedVar."
                "%s fails this criterion." % parameter)
        if var == parameter.parameter:
            # For example: 1_1, ..., n_n is not allowed.
            raise ValueError(
                "Parameter, %s, not valid, indexing a range parameter "
                "variable" % parameter)
        return var
    elif isinstance(parameter, IndexedVar):
        if _required_indices is not None:
            """
            if not _required_indices.issuperset(parameter.indices):
                # TODO: WHAT ABOUT STATIC INDICES; for example, x_1
                unexpected_indices = (set(parameter.indices) 
                                      - _required_indices)
                if len(unexpected_indices) > 1:
                    msg = ("%s were not expected parameter indices"
                           %unexpected_indices)
                else:
                    msg = ("%s is not an expected parameter index"
                           %next(iter(unexpected_indices)))
                raise ValueError(msg + " of %s, expecting %s."%(parameter,
                                                               _required_indices))
            """
            _required_indices.difference_update(parameter.indices)
        return parameter.var
    elif isinstance(parameter, Variable):
        return parameter
    else:
        raise TypeError('Parameter must be a Variable, Indexed variable, or '
                        'range (ExprRange) over Indexed variables.  %s fails '
                        'to meet this requirement.' % parameter)


def valid_params(expr_tuple):
    '''
    Return True iff all the entries of the given "expr_tuple" form a
    valid tuple of parameters.
    '''
    # See if this is an allowed expansion of a
    # range of parameters.
    try:
        expanded_vars = {get_param_var(expanded_param)
                         for expanded_param in expr_tuple.entries}
        if len(expanded_vars) != len(expr_tuple.entries):
            # Parameter variables must be unique to be valid.
            return False
        # All valid and unique parameter entries.
        return True
    except TypeError:
        # One of the entries is not valid.
        return False


class Lambda(Expression):
    '''
    A lambda-function Expression.  A lambda function maps parameter(s) to
    its body.  For example, (x, y) -> sin(x^2 + y), where (x, y) are the
    parameters and sin(x^2 + y) is the body.  Each parameter must be a
    Variable.  Note that the body of a Lambda may be a Conditional
    such that the mapping is only defined when one of the conditions is
    satisfied.
    '''

    def __init__(self, parameter_or_parameters, body, *, styles=None):
        '''
        Initialize a Lambda function expression given parameter(s) and a
        body. Each parameter must be a Variable or a range (ExprRange)
        of indexed variables (IndexedVar).
        When there is a single parameter, there will be a 'parameter'
        attribute. Either way, there will be a 'parameters' attribute
        that bundles the one or more Variables into an ExprTuple.
        The 'body' attribute will be the lambda function body
        Expression.  The body may be singular or a composite.
        '''
        from proveit._core_.expression.label.var import Variable
        from proveit._core_.expression.composite import (
            composite_expression, single_or_composite_expression)
        self.parameters = composite_expression(parameter_or_parameters)
        parameter_vars = [get_param_var(parameter)
                          for parameter in self.parameters]
        if is_single(self.parameters):
            # has a single parameter
            self.parameter = self.parameters[0]
            self.parameter_or_parameters = self.parameter
        else:
            self.parameter_or_parameters = self.parameters
        self.parameter_vars = tuple(parameter_vars)
        self.parameter_var_set = frozenset(parameter_vars)

        # Parameter variables may not occur multiple times.
        if len(self.parameter_var_set) != self.parameters.num_entries():
            raise ParameterCollisionError(
                self.parameters, "Parameter variables must be unique")

        # Parameter variables may not occur as free variables of
        # any of the parameter indexes.
        free_vars_of_param_indices = \
            self._free_vars_of_parameter_indices()
        if not free_vars_of_param_indices.isdisjoint(self.parameter_var_set):
            raise ParameterCollisionError(
                self.parameters, ("Parameter variables may not occur as "
                                  "free variables in parameter indices"))

        # Note: a Lambda body may be an ExprRange which is useful
        # for making nested ranges of ranges.
        # However, this must not be allowed in the "operation 
        # substitution" reduction (in Operation.basic_replaced)
        # because it does not respect arity of the function outcome.
        # Without such a restriction you end up being able to prove
        # |f_1(i_1), ..., f_1(j_1), ......, f_n(i_n), ..., f_n(j_n)| = n
        # WHICH WOULD BE WRONG, IN GENERAL!
        body = single_or_composite_expression(body,
                                              wrap_expr_range_in_tuple=False)
        # After the single_or_composite_expression, this assertion should
        # not fail.
        assert isinstance(body, Expression)
        self.body = body

        # For any parameter that is a range of indexed variables
        # (or just an indexed variable), make sure that corresponding
        # parameter variable does not occur in a non-indexed form
        # in the body.  For example, forall_{b_1, ..., b_n} f(b)
        # is not a valid form.
        for param, param_var in zip(self.parameters, self.parameter_vars):
            if not isinstance(param, Variable):
                body_var_ranges = body._free_var_ranges()
                if param_var in body_var_ranges:
                    if param_var in body_var_ranges[param_var]:
                        raise ValueError(
                            "With %s being parameterized, %s may not occur "
                            "in a non-indexed form in the body: %s"
                            %(param, param_var, body))
        sub_exprs = (self.parameters, self.body)
        Expression.__init__(self, ['Lambda'], sub_exprs, styles=styles)
        # Increase the number of potentially-independent internal bound
        # variables; this count will help produce a canonical form.
        self._num_indep_internal_bound_vars += self.parameters.num_entries()

    @classmethod
    def _make(sub_class, core_info, sub_expressions, *, styles):
        if len(core_info) != 1 or core_info[0] != 'Lambda':
            raise ValueError(
                "Expecting Lambda core_info to contain exactly one "
                "item: 'Lambda'")
        if sub_class != Lambda:
            raise MakeNotImplemented(sub_class)
        if len(sub_expressions) != 2:
            raise ValueError("Expected Lambda to have two sub-expressions")
        parameters, body = sub_expressions
        return Lambda(parameters, body, styles=styles)

    def _free_vars_of_parameter_indices(self):
        '''
        Return the set of free variables of the indices of all
        of the parameters of this Lambda expression.
        '''
        from proveit._core_.expression.composite import ExprRange
        from proveit._core_.expression.operation.indexed_var import IndexedVar
        free_vars_of_indices = set()
        for parameter in self.parameters:
            if (isinstance(parameter, ExprRange) and
                    isinstance(parameter.body, IndexedVar)):
                free_vars_of_indices.update(
                    free_vars(parameter.true_start_index))
                free_vars_of_indices.update(
                    free_vars(parameter.true_end_index))
            elif isinstance(parameter, IndexedVar):
                free_vars_of_indices.update(
                    free_vars(parameter.index))
        return free_vars_of_indices
    
    def canonically_labeled(self):
        return self._canonically_labeled_lambda()

    def _canonically_labeled_lambda(self):
        '''
        Retrieve (and create if necessary) the canonical version of this
        Lambda expression in which its parameters are replaced with
        deterministic 'dummy' variables.
        '''
        from proveit._core_.expression.operation.indexed_var import (
            IndexedVar)

        if hasattr(self, '_canonically_labeled'):
            return self._canonically_labeled

        # Relabel parameter variables to something deterministic
        # independent of the original labels.
        parameter_vars = self.parameter_vars
        parameters = self.parameters
        effective_param_vars = []
        for param, param_var in zip(parameters, parameter_vars):
            if isinstance(param, IndexedVar):
                # There is an IndexedVar parameter (e.g., x_1).
                # To be a proper form, the only occurrence of x in
                # the body must be x_1 and we should relabel it to a
                # simple variable in the canonical form.
                forms_dict = self.body._free_var_ranges()
                var_forms = forms_dict.get(param_var, {param})
                if var_forms != {param}:
                    # Invalid form
                    raise ParameterMaskingError(
                        "With a %s parameter, the body of %s should "
                        "only contain occurrences of %s of the form %s "
                        "but contains all of these forms: %s"
                        %(param, self, param_var, param, var_forms))
                effective_param_vars.append(param)
            else:
                effective_param_vars.append(param_var)
                
        # Assign canonical labels to the parameters using the first
        # non-contestable dummy variable (using the number of
        # potentially-independent interanlly bound variables to
        # determine what may be contestable), skipping over free 
        # variables that happen to match any of these dummy variables.
        canonical_parameters = parameters.canonically_labeled()
        canonical_body = self.body.canonically_labeled()
        canonical_body_free_vars = free_vars(canonical_body)
        canonical_parameters_free_vars = free_vars(canonical_parameters)
        lambda_free_vars = set(canonical_body_free_vars)
        lambda_free_vars.update(canonical_parameters_free_vars)
        lambda_free_vars.difference_update(effective_param_vars)
        start_index = self.body._num_indep_internal_bound_vars
        dummy_index = 0
        while dummy_index < start_index:
            dummy_var = safe_dummy_var(
                start_index=dummy_index,
                avoid_default_assumption_conflicts=False)
            if dummy_var in lambda_free_vars:
                start_index += 1
            dummy_index += 1
        canonical_param_vars = list(reversed(
            safe_dummy_vars(
                len(effective_param_vars), *lambda_free_vars,
                start_index=start_index,
                avoid_default_assumption_conflicts=False)))

        with defaults.temporary() as temp_defaults:
            # Don't auto-reduce or use automation when making the
            # canonical version.  Also, don't apply "consistent
            # styles" -- we need use "canonical" styles.
            temp_defaults.automation = False
            temp_defaults.auto_simplify = False
            temp_defaults.assumptions = tuple()
            #temp_defaults.use_consistent_styles = False
            # Canonical Lambda styles are always empty.
            canonical_styles = dict()
            if canonical_param_vars != effective_param_vars:
                # Create the canonical version via relabeling.
                relabel_map = \
                    {param_var: canonical_param_var
                     for param_var, canonical_param_var
                     in zip(effective_param_vars, canonical_param_vars)}
                canonical_parameters = parameters.basic_replaced(
                    relabel_map).canonically_labeled()
                canonical_body = canonical_body.basic_replaced(
                    relabel_map).canonically_labeled()
                canonically_labeled = Lambda(canonical_parameters, 
                                            canonical_body)
            elif (self._style_data.styles == canonical_styles and
                  canonical_body._style_id == self.body._style_id and
                  canonical_parameters._style_id == self.parameters._style_id):
                canonically_labeled = self
            else:
                canonically_labeled = Lambda(canonical_parameters, 
                                            canonical_body)
        self._canonically_labeled = canonically_labeled
        canonically_labeled._canonically_labeled = canonically_labeled
        return canonically_labeled

    def _build_canonical_form(self):
        '''
        Build the canonical form of this Lambda.
        This override Expression._build_canonical_form to leave
        parameters unchanged.
        '''
        canonically_labeled = self.canonically_labeled()
        if canonically_labeled != self:
            # We need to use canonical labels to ensure
            # consistency of cnaonical forms.
            return canonically_labeled._build_canonical_form()
        # Leave the parameters unchanged:
        canonical_sub_exprs = [self.parameters]
        has_distinct_canonical_form = False
        for sub_expr in self._sub_expressions[1:]:
            canonical_sub_expr = sub_expr.canonical_form()
            if sub_expr != canonical_sub_expr:
                has_distinct_canonical_form = True
            canonical_sub_exprs.append(canonical_sub_expr)
        if has_distinct_canonical_form:
            # Use the canonical forms of the sub-expressions.
            return self._checked_make(
                self._core_info, canonical_sub_exprs,
                style_preferences=self._style_data.styles)
        else:
            # No canonical form that is different from self.
            return self        

    def extract_argument(self, mapped_expr):
        '''
        Given a mapped expression, return the argument that will transform
        this Lambda expression into the mapped expression.  For example,
        if the Lambda expression is x -> x + 1 and the mapped expression
        is 2 + 1, this will return 2.  If there is more than one parameter
        in this Lambda expression, use extract_arguments instead.
        '''
        assert is_single(self.parameters), (
                "Use the 'extract_arguments' method when there is more "
                "than one parameter")
        return self.extract_arguments(mapped_expr)[0]

    def extract_arguments(self, mapped_expr):
        '''
        Given a mapped expression, return the arguments that will transform
        this Lambda expression into the mapped expression.  For example,
        if the Lambda expression is (x, y) -> x + y and the mapped expression
        is 1 + 2, this will return (1, 2).
        '''
        # Perform a simulataneous depth-first search to find the parameters
        # of the lambda map and corresponding values from the mapped_expr.
        parameters = self.parameters
        lambda_sub_expr = self.body
        mapped_sub_expr = mapped_expr
        if self.parameters.num_entries() == 1 and self.body == self.parameter:
            # Simple case of x -> x.  Just return the mapped_expr as the
            # one argument.
            return [mapped_expr]
        param_values = [None] * parameters.num_entries()
        if lambda_sub_expr.num_sub_expr() != mapped_sub_expr.num_sub_expr():
            raise ArgumentExtractionError("# of sub-expressions, %d vs %d"
                                          % (lambda_sub_expr.num_sub_expr(),
                                             mapped_sub_expr.num_sub_expr()))
        if lambda_sub_expr.__class__ != mapped_sub_expr.__class__:
            raise ArgumentExtractionError("Expression class, %s vs %s"
                                          % (str(lambda_sub_expr.__class__),
                                             str(mapped_sub_expr.__class__)))
        if lambda_sub_expr._core_info != mapped_sub_expr._core_info:
            raise ArgumentExtractionError("core information, %s vs %s"
                                          % (str(lambda_sub_expr._core_info),
                                             str(mapped_sub_expr._core_info)))
        lambda_sub_expr_iters = [lambda_sub_expr.sub_expr_iter()]
        mapped_sub_expr_iters = [mapped_sub_expr.sub_expr_iter()]
        while len(lambda_sub_expr_iters) > 0:
            try:
                lambda_sub_expr = next(lambda_sub_expr_iters[-1])
                mapped_sub_expr = next(mapped_sub_expr_iters[-1])
                extraction_err = ArgumentExtractionError  # abbreviation
                if lambda_sub_expr in parameters:
                    # found a match
                    param_idx = parameters.index(lambda_sub_expr)
                    if param_values[param_idx] is not None \
                            and param_values[param_idx] != mapped_sub_expr:
                        raise extraction_err("inconsistent parameters values, "
                                             "%s vs %s"
                                             % (str(param_values[param_idx]),
                                                str(mapped_sub_expr)))
                    param_values[param_idx] = mapped_sub_expr
                else:
                    if lambda_sub_expr.num_sub_expr() != mapped_sub_expr.num_sub_expr():
                        raise extraction_err(
                            "# of sub-expressions, %d vs %d" %
                            (lambda_sub_expr.num_sub_expr(), mapped_sub_expr.num_sub_expr()))
                    if lambda_sub_expr.__class__ != mapped_sub_expr.__class__:
                        raise extraction_err(
                            "Expression class, %s vs %s" %
                            (str(
                                lambda_sub_expr.__class__), str(
                                mapped_sub_expr.__class__)))
                    if lambda_sub_expr._core_info != mapped_sub_expr._core_info:
                        raise extraction_err(
                            "core information, %s vs %s" %
                            (str(
                                lambda_sub_expr._core_info), str(
                                mapped_sub_expr._core_info)))
                    if lambda_sub_expr.num_sub_expr() > 0:
                        # going deeper
                        lambda_sub_expr_iters.append(
                            lambda_sub_expr.sub_expr_iter())
                        mapped_sub_expr_iters.append(
                            mapped_sub_expr.sub_expr_iter())
            except StopIteration:
                # exhausted the "deepest" of the sub-expressions
                # pop back out to a shallower level
                lambda_sub_expr_iters.pop(-1)
                mapped_sub_expr_iters.pop(-1)
        return param_values

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the Lambda expression.
        '''
        yield self.parameter_or_parameters
        yield self.body

    def string(self, **kwargs):
        return Lambda._string(self.parameters, self.body, **kwargs)

    @staticmethod
    def _string(parameters, body, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        out_str = '[' if fence else ''
        parameter_list_str = ', '.join(
            [parameter.string(abbrev=True) for parameter in parameters])
        if is_single(parameters):
            out_str += parameter_list_str + ' -> '
        else:
            out_str += '(' + parameter_list_str + ') -> '
        out_str += body.string(fence=True)
        if fence:
            out_str += ']'
        return out_str

    def latex(self, **kwargs):
        fence = kwargs['fence'] if 'fence' in kwargs else False
        out_str = r'\left[' if fence else ''
        parameter_list_str = ', '.join(
            [parameter.latex(abbrev=True) for parameter in self.parameters])
        if is_single(self.parameters):
            out_str += parameter_list_str + r' \mapsto '
        else:
            out_str += r'\left(' + parameter_list_str + r'\right) \mapsto '
        out_str += self.body.latex(fence=True)
        if fence:
            out_str += r'\right]'
        return out_str

    def apply(self, *operands, param_to_num_operand_entries=None,
              equiv_alt_expansions=None,
              allow_relabeling=False, assumptions=USE_DEFAULTS, 
              requirements=None):
        '''
        Apply this lambda map onto the given operands (a beta reduction
        in the lambda calculus terminology), returning the
        expression that results from applying the map.  Assumptions
        may be necessary to prove requirements that will be passed back
        if a requirements list is provided.  Requirements may be needed
        to ensure that operands are an appropriate length to match
        a corresponding ExprRange of parameters.  Specifically, the Len
        of an ExprTuple containing the operands must equal the Len of an
        ExprTuple containing the range of indices covered by a
        corresponding parameter range (see the example below).  Full
        automation of the  length proof will only be performed for the
        last parameter entry; proving the length equivalence may need to
        be performed in advance.

        For example, applying the Lambda
        (x, y_1, ..., y_3, z_i, ..., z_j) ->
            x*y_1 + ... + x*y_3 + z_i + ... + z_j
        to operands (a, b, c, d, e_m, ..., e_n, f)
        will result in a*b + a*c + a*d + e_m + ... _ e_n + f provided
        that|(b, c, d)| = |(1, ..., 3)| is proven in advance and that
        |(e_m, ..., e_n, f)| = |(i, ..., j)| can be proven via
        automation.

        A dictionary may be provided for equiv_alt_expansions to
        accomplish instantiation of ranges of parameters with more
        versatility.  For example, given the following Lambda
        (x_1, ..., x_{n+1}) -> (x_1 < x_{1+1}) and ...
                                   and (x_n < x_{n+1})
        we can apply this on the following operands:
            (a_1, ..., a_{k+1}, b_1, ..., b_{n-k})
        along with the following entries in equiv_alt_expansions
        (x_1, ..., x_n, x_{n+1}) :
            (a_1, ..., a_k, a_{k+1}, b_1, ..., b_{n-k-1}, b_{n-k})
        (x_1, x_{1+1}, ..., x_{n+1}) :
            (a_1, a_{1+1}, ..., a_{k+1}, b_1,
             b_{1+1}, ..., b_{(n-k-1)+1})
        to obtain
        (a_1 < a_{1+1}) and ... and (a_k < a_{k+1}) and a_k < b_1
            and (b_1 < b_{1+1}) and ... and (b_{n-k-1} < b_{(n-k-1)+1})
        under the following requirements:
        |(a_1, ..., a_{k+1}, b_1, ..., b_{n-k})| = |(1, ..., n+1)|
        (1, ..., n) = (1, ..., n, n+1)
        (1, ..., n) = (1, 1+1, ..., n+1)
        (a_1, ..., a_{k+1}, b_1, ..., b_{n-k})
            = (a_1, ..., a_k, a_{k+1}, b_1, ..., b_{n-k-1}, b_{n-k})
        (a_1, ..., a_{k+1}, b_1, ..., b_{n-k})
            = (a_1, a_{1+1}, ..., a_{k+1}, b_1,
               b_{1+1}, ..., b_{(n-k-1)+1})
        |({a_1, ..., a_k, a_{k+1}, b_1, ..., b_{n-k-1})|
            = |(1, ..., n)|
        |(a_{1+1}, ..., a_{k+1}, b_1, b_{1+1}, ..., b_{(n-k-1)+1})|
            = |(1+1, ..., n+1)|

        If allow relabeling is True then inn

        There are limitations with respect the Lambda map application
        involving parameter ranges when perfoming operation
        substitution in order to keep derivation rules (i.e.,
        instantiation) simple.  For details, see the
        ExprRange.replaced documentation.

        There may be additional requirements introduced when expanding
        ranges.  For example, indices may need to match, not just
        lengths.
        '''
        if assumptions is not USE_DEFAULTS:
            with defaults.temporary() as temp_defaults:
                temp_defaults.assumptions = assumptions
                return Lambda._apply(
                    self.parameters, self.body, *operands,
                    param_to_num_operand_entries=param_to_num_operand_entries,
                    equiv_alt_expansions=equiv_alt_expansions,
                    allow_relabeling=allow_relabeling, 
                    requirements=requirements,
                    parameter_vars=self.parameter_vars)
        return Lambda._apply(
            self.parameters, self.body, *operands,
            param_to_num_operand_entries=param_to_num_operand_entries,
            equiv_alt_expansions=equiv_alt_expansions,
            allow_relabeling=allow_relabeling, requirements=requirements,
            parameter_vars=self.parameter_vars)

    @staticmethod
    def _apply(parameters, body, *operands, 
               param_to_num_operand_entries=None, 
               equiv_alt_expansions=None,
               allow_relabeling=False, requirements=None,
               parameter_vars=None):
        '''
        Static method version of Lambda.apply which is convenient for
        doing 'apply' with an 'on-the-fly' effective Lambda that does
        not need to be initialized (for the sake of efficiency for an
        Instantiation proof).  It also has the flexibility of allowing
        an initial 'repl_map' to start with, which will me amended
        according to paramater:operand mappings.
        '''
        from proveit import ExprTuple, extract_var_tuple_indices
        from proveit.logic import Equals
        
        # derive side-effects if applicable
        defaults.make_assumptions()

        try:
            if parameter_vars is None:
                parameter_vars = \
                    [get_param_var(parameter) for parameter in parameters]
        except TypeError as e:
            raise TypeError("Invalid ad-hoc Lambda parameters, %s:\n%s"
                            % (parameters, str(e)))

        # We will be appending to the requirements list if it is given
        # (or a throw-away list if it is not).
        if requirements is None:
            requirements = []

        # We will be matching operands with parameters in the proper
        # order and adding corresponding entries to the replacement map.
        repl_map = dict()
        extract_complete_param_replacements(
            parameters, parameter_vars, body, operands,
            param_to_num_operand_entries, requirements, repl_map)

        # Add repl_map entries resulting from equiv_alt_expansions.

        # For updating the repl_map:
        repl_map_extensions = dict()
        # Map variables to sets of tuples representing that variable
        # being consecutively indexed over the same range as in the
        # parameters.  `repl_map` will be updated with this information.
        var_range_forms = dict()
        if equiv_alt_expansions is not None:
            if not isinstance(equiv_alt_expansions, dict):
                raise TypeError("'equiv_alt_expansions' must be a dict")
            for var_tuple, expansion_tuple in equiv_alt_expansions.items():
                if not isinstance(var_tuple, ExprTuple):
                    raise TypeError("'equiv_alt_expansions' keys must be "
                                    "ExprTuple objects; %s is a %s."
                                    % (var_tuple, var_tuple.__class__))
                if not isinstance(expansion_tuple, ExprTuple):
                    raise TypeError("'equiv_alt_expansions' values must be "
                                    "ExprTuple objects; %s is a %s."
                                    % (expansion_tuple,
                                       expansion_tuple.__class__))
                param_var = None
                for var_tuple_entry in var_tuple:
                    try:
                        if param_var is None:
                            param_var = get_param_var(var_tuple_entry)
                        else:
                            if get_param_var(var_tuple_entry) != param_var:
                                raise ValueError
                    except (TypeError, ValueError):
                        raise ValueError(
                            "'equiv_alt_expansions' values must be "
                            "a tuple containing variables, indexed "
                            "variables, or ranges of indexed variables "
                            "all of the same variable and with no "
                            "internal shifts.  %s does not "
                            "meet this requirement." % var_tuple)
                expansion_set = repl_map.get(param_var, None)
                if expansion_set is None:
                    raise LambdaApplicationError(
                        parameters, body, operands, equiv_alt_expansions,
                        "'equiv_alt_expansions' values must represent "
                        "a tuple of consecutive indexed variables that "
                        "corresponds with a range of parameters "
                        "(with no shift in ExprRange indices): "
                        "%s is not found in %s."
                        % (var_tuple, repl_map.keys()))
                # We need to ensure that the tuples of indices match.
                orig_params = list(expansion_set)[0]
                indices_eq_req = Equals(extract_var_tuple_indices(var_tuple),
                                        extract_var_tuple_indices(orig_params))
                if indices_eq_req.lhs != indices_eq_req.rhs:
                    requirements.append(indices_eq_req.prove())
                # We need to ensure that the tuple expansions are equal.
                orig_expansion = repl_map[orig_params]
                eq_expansion_req = Equals(expansion_tuple, orig_expansion)
                if eq_expansion_req.lhs != eq_expansion_req.rhs:
                    requirements.append(eq_expansion_req.prove())
                # Now add new entries to repl_map_extensions for the
                # new expansion and components corresponding to the
                # components of the var_tuple.
                cur_repl_map_extensions = dict()
                cur_repl_map_extensions[var_tuple] = expansion_tuple
                try:
                    extract_complete_param_replacements(
                        var_tuple, [param_var] * var_tuple.num_entries(),
                        var_tuple, expansion_tuple, None,
                        requirements, cur_repl_map_extensions)
                except LambdaApplicationError as e:
                    raise LambdaApplicationError(
                        parameters, body, operands, equiv_alt_expansions,
                        "Unable to match 'equiv_alt_expansions' "
                        "values entries to a key entry for key & value "
                        "%s & %s.\n%s."
                        % (var_tuple, expansion_tuple, str(e)))
                # Update 'var_tuple_map'
                if param_var not in var_range_forms:
                    var_range_forms[param_var] = set(expansion_set)
                var_range_forms[param_var].add(var_tuple)
                repl_map_extensions.update(cur_repl_map_extensions)

        if len(repl_map_extensions) > 0:
            repl_map.update(repl_map_extensions)
            repl_map.update(var_range_forms)
        try:
            return body.basic_replaced(
                repl_map, allow_relabeling=allow_relabeling, 
                requirements=requirements)
        except ImproperReplacement as e:
            raise LambdaApplicationError(
                parameters, body, operands, equiv_alt_expansions,
                "Improper replacement: %s " % str(e))
        except TypeError as e:
            raise LambdaApplicationError(
                parameters, body, operands, equiv_alt_expansions,
                "TypeError: %s " % str(e))

    def basic_replaced(self, repl_map, *,
                       allow_relabeling=False, requirements=None):
        '''
        Returns this expression with sub-expressions replaced
        according to the replacement map (repl_map) dictionary
        which maps Expressions to Expressions.

        If allow_relabeling is True then internal Lambda parameters
        may be replaced when it is a valid replacement of parameter(s)
        (i.e., Variable's, IndexedVar's, or an ExprRange of
        IndexedVar's, and unique parameter variables).
        Otherwise, the Lambda parameter variables will be masked
        within its scope.  Partial masked of a range of indexed
        varaibles is not allowed and will cause an error.
        For example, we cannot replace (x_1, ..., x_{n+1}) within
        (x_1, ..., x_n) -> f(x_1, ..., x_n).

        'requirements' (and defaults.assumptoins) are used when an 
        operator is replaced by a Lambda map that has a range of
        parameters (e.g., x_1, ..., x_n) such that the length of the
        parameters and operands must be proven to be equal.  For more 
        details, see Operation.replaced, Lambda.apply, and
        ExprRange.replaced (which is the sequence of calls involved).
        '''
        if len(repl_map) > 0 and (self in repl_map):
            # The full expression is to be replaced.
            return repl_map[self]

        # Use a helper method to handle some inner scope 
        # transformations.
        new_params, inner_repl_map, inner_assumptions = self._inner_scope_sub(
                repl_map, allow_relabeling, requirements)

        # The lambda body with the substitutions.
        with defaults.temporary() as temp_defaults:
            temp_defaults.assumptions = inner_assumptions
            subbed_body = self.body.basic_replaced(
                inner_repl_map, allow_relabeling=allow_relabeling, 
                requirements=requirements)

        try:
            replaced = Lambda(new_params, subbed_body)
        except TypeError as e:
            raise ImproperReplacement(self, repl_map, e.args[0])
        except ValueError as e:
            raise ImproperReplacement(self, repl_map, e.args[0])

        return replaced

    def _auto_simplified_sub_exprs(self, *, requirements, stored_replacements,
                                   markers_and_marked_expr):
        '''
        Properly handle the Lambda scope while doing auto-simplification
        replacements.  Also, don't replace parameter variables.
        '''
        # Can't use assumptions involving lambda parameter variables
        inner_assumptions = \
            [assumption for assumption in defaults.assumptions if
             free_vars(assumption).isdisjoint(self.parameter_vars)]        
        with defaults.temporary() as temp_defaults:
            temp_defaults.assumptions = inner_assumptions
            # Since the assumptions have changed, we can no longer use
            # the stored_replacements from before.
            subbed_body = self.body._auto_simplified(
                    requirements=requirements, 
                    stored_replacements=dict(),
                    markers_and_marked_expr=self._update_marked_expr(
                            markers_and_marked_expr, 
                            lambda _expr : _expr.body))
            if subbed_body == self.body:
                # Nothing change, so don't remake anything.
                return self                
            # Don't replace parameter variables.
            subbed_sub_exprs = (self.parameters, subbed_body)
            return self.__class__._checked_make(
                    self._core_info, subbed_sub_exprs,
                    style_preferences=self._style_data.styles)

    def _inner_scope_sub(self, repl_map, allow_relabeling, requirements):
        '''
        Helper method for basic_replaced (and used by 
        ExprRange._replaced_entries) which handles the change in scope 
        properly as well as parameter relabeling.
        '''
        from proveit import (Variable, ExprTuple, ExprRange, IndexedVar,
                             simplified_indices)
        from proveit._core_.expression.composite.expr_range import \
            extract_start_indices, extract_end_indices, var_range

        parameter_vars = self.parameter_vars
        # Free variables of the body but excluding the parameter
        # variables.
        non_param_body_free_vars = (free_vars(self.body)
                                    - self.parameter_var_set)

        # First, we may replace indices of any of the parameters.
        parameters = []
        var_to_param = dict()
        for param in self.parameters:
            if isinstance(param, IndexedVar):
                subbed_index = param.index.basic_replaced(
                        repl_map, allow_relabeling=allow_relabeling, 
                        requirements=requirements)
                param_var = param.var
                param = IndexedVar(param_var, subbed_index)
            elif isinstance(param, ExprRange):
                param_var = get_param_var(param)
                subbed_start = \
                    ExprTuple(*extract_start_indices(param)).basic_replaced(
                        repl_map, allow_relabeling=allow_relabeling, 
                        requirements=requirements)
                subbed_end = \
                    ExprTuple(*extract_end_indices(param)).basic_replaced(
                        repl_map, allow_relabeling=allow_relabeling, 
                        requirements=requirements)
                subbed_start, subbed_end = simplified_indices(
                    subbed_start, subbed_end, requirements=requirements)
                range_param = var_range(param_var, subbed_start, subbed_end)
                param = range_param
            else:
                param_var = param
            parameters.append(param)
            var_to_param[param_var] = param

        # Within the lambda scope, we can instantiate lambda parameters
        # in a manner that retains the validity of the parameters as
        # parameters.  For any disallowed instantiation of Lambda
        # parameters, we will ignore the corresponding instantiation
        # within this scope and assume it is meant to be done external
        # to this scope; it is masked within the new scope with
        # exception to a partial masking of a range of indexed
        # variables.  In the latter case, we raise an exception,
        # disallowing such substitutions.
        inner_repl_map = dict()
        relabel_map = dict()
        for key, value in repl_map.items():
            if not free_vars(key).isdisjoint(self.parameter_var_set):
                # If any of the free variables of the key occur as
                # parameter variables, either that replacement is
                # masked within this scope, or there is an allowed
                # relabeling or parameter range expansion.

                # First, let's see if there is an associated
                # expansion for this key.
                tmp_replacement = None
                if (isinstance(key, Variable) and 
                        isinstance(value, ExprTuple)):
                    if key in var_to_param:
                        # Relabel a range of parameters via a 
                        # replacement for just a variable.
                        param_of_var = var_to_param[key]
                        if isinstance(param, IndexedVar):
                            if value.num_entries()>0:
                                # May relabel a parameter entry that 
                                # becomes an IndexedVar with the first
                                # entry of the variable's replacement.
                                key = param
                                value = value[0]
                        else:
                            # May relabel a range of parameters
                            # acccording to the variable's tuple
                            # replacement.
                            param_tuple = ExprTuple(param_of_var)
                            if param_tuple not in repl_map:
                                tmp_replacement = value
                            value = {param_tuple}
                if isinstance(value, set):
                    # There are one or more expansions for a variable
                    # that occurs as a local Lambda parameter.
                    # It may be fully or partially masked.  We have to
                    # be careful about partial masks, making sure
                    # there is no masking outside of the covered range
                    # of indices but there is masking otherwise.
                    var = key
                    assert isinstance(var, Variable)
                    if var in var_to_param:
                        param_of_var = var_to_param[var]
                    else:
                        # The key is not being masked in any way,
                        # so just carry this through to the
                        inner_repl_map[key] = value # inner_repl_map.
                        continue
                    if isinstance(param_of_var, Variable):
                        # The parameter is the Variable itself, so
                        # it masks all occurrences of that Variable.
                        continue  # No inner replacement for this.
                    # We may relabel or mask the full range
                    # of parameters (but partial masking is
                    # not allowed!).
                    var_range_forms = value
                    var_range_form = ExprTuple(param_of_var)
                    if var_range_form not in var_range_forms:
                        raise ImproperReplacement(
                            self, repl_map, 
                            ("Partial masking not allowed. "
                             "%s is not in %s"
                             %(param_of_var, var_range_forms)))
                    if tmp_replacement is not None:
                        _replacement = tmp_replacement
                    else:
                        _replacement = repl_map[var_range_form]
                    if allow_relabeling and valid_params(_replacement):
                        relabel_map[var] = value
                        relabel_map[var_range_form] = _replacement
                elif isinstance(key, Variable) and isinstance(value, Variable):
                    # A simple relabeling is allowed to propagate
                    # through.
                    if allow_relabeling:
                        relabel_map[key] = value
                    # Otherwise, it is a simple, fair masking.
                elif (isinstance(key, IndexedVar) and key in parameters):
                    if allow_relabeling:
                        if (isinstance(value, IndexedVar)
                                or isinstance(value, Variable)):
                            # You can relabel an IndexedVar to another
                            # IndexedVar or a Variable.
                            relabel_map[key] = value
                    # Otherwise, it is a simple, fair masking.
                # In all remaining cases where the key is not
                # inserted into inner_repl_map, the replacement
                # is deemed to be safely masked within this scope.
            else:
                # No conflict -- propagate the replacement
                try:
                    key_var = get_param_var(key)
                except (ValueError, TypeError):
                    key_var = None
                if key_var is None:
                    # Non parameter-like key -- just push through.
                    inner_repl_map[key] = value
                elif key_var in non_param_body_free_vars:
                    # This may replace a free variable in the body.
                    inner_repl_map[key] = value
                else:
                    # This does not replace a free variable in the
                    # body, but may relabel something internally.
                    # We put this in the relabel_map instead of the
                    # inner_repl_map so it doesn't impact 
                    # 'restricted_vars' below.
                    relabel_map[key] = value                        

        # Free variables of the replacements must not collide with
        # the parameter variables.  If there are collisions, relabel
        # the parameter variables to something safe.  First, get the
        # free variables of the body and the replacements.
        # (Note: a repl_map 'value' may be a set indicating
        # possible expansions for an indexed variable over a range,
        # e.g., x : {(x_1, .., x_{n+1}), ({x_1, .., x_n}),
        #            (x_{1+1}, ..., x_{n+1})}
        # we can ignore those for this purpose as the real replacements
        # will be what the members of this set map to.
        restricted_vars = non_param_body_free_vars - inner_repl_map.keys()
        restricted_vars.update(
            *[free_vars(value) for key, value in inner_repl_map.items()
              if (key not in self.parameter_var_set
                  and not isinstance(value, set))])
        for param, param_var in zip(parameters, parameter_vars):
            if isinstance(param, IndexedVar):
                param_var_repl = relabel_map.get(param, param_var)
                if isinstance(param_var_repl, IndexedVar):
                    param_var_repl = get_param_var(param_var_repl)
            else:
                param_var_repl = relabel_map.get(param_var, param_var)
            if param_var_repl in restricted_vars:
                dummy_var = safe_dummy_var(
                    *restricted_vars,
                    avoid_default_assumption_conflicts=False)
                if isinstance(param, IndexedVar):
                    relabel_map[param] = dummy_var
                else:
                    relabel_map[param_var] = dummy_var
                restricted_vars.add(dummy_var)
            else:
                if isinstance(param_var_repl, set):
                    # If param_var_repl is a set, it's for possible
                    # expansions of an indexed variable.  For the
                    # purpose of checking collisions, we just want
                    # the variable being indexed.
                    restricted_vars.add(param_var)
                else:
                    restricted_vars.add(param_var_repl)
        inner_repl_map.update(relabel_map)

        # Generate the new set of parameters which may be relabeled
        # or may be expanded.
        # For example, we may have
        # x_1, ..., x_3 go to
        #       a, b, c with (x_1, ..., x_3):(a, b, c)
        new_params = []
        
        for parameter, param_var in zip(parameters, parameter_vars):
            if isinstance(parameter, ExprRange):
                for subbed_param in parameter._replaced_entries(
                        inner_repl_map, allow_relabeling,
                        requirements):
                    new_params.append(subbed_param)
            else:
                subbed_param = parameter.basic_replaced(
                    inner_repl_map, allow_relabeling=allow_relabeling,
                    requirements=requirements)
                new_params.append(subbed_param)

        if len({get_param_var(param)
                for param in new_params}) != len(new_params):
            raise ParameterCollisionError(
                new_params, "Parameter variables must be unique")

        # Can't use assumptions involving lambda parameter variables
        new_param_vars = [get_param_var(new_param) for new_param in new_params]
        inner_assumptions = \
            [assumption for assumption in defaults.assumptions if
             free_vars(assumption).isdisjoint(new_param_vars)]
        
        return new_params, inner_repl_map, tuple(inner_assumptions)

    def relabeled(self, relabel_map):
        '''
        Return a variant of this Lambda expression with one or more
        of its parameter labels changed.  The resulting expression
        should be "equal" to the original (having the same meaning) but
        essentially has a different "style" (formats differently) and
        uses different labels for substitution purposes.
        '''
        from proveit import Variable, IndexedVar
        for key, val in relabel_map.items():
            if (not isinstance(val, Variable)
                    and not isinstance(val, IndexedVar)):
                raise TypeError("May only relabel Variables/IndexedVars "
                                "to Variables/IndexedVars; "
                                "may not relabel %s" % val)
            if (not isinstance(val, Variable)
                    and not isinstance(val, IndexedVar)):
                raise TypeError("May only relabel Variables/IndexedVars "
                                "to Variables/IndexedVars; "
                                "may not relabel to %s" % key)
        relabeled = self.basic_replaced(relabel_map, allow_relabeling=True)
        for orig_param_var, new_param_var in zip(self.parameter_vars,
                                                 relabeled.parameter_vars):
            # Check that the relabeling happened properly.
            if (new_param_var !=
                    relabel_map.get(orig_param_var, orig_param_var)):
                raise ParameterRelabelingError(self, relabel_map)
        assert relabeled == self, (
            "Relabeled version should be 'equal' to original")
        return relabeled

    @equality_prover('simplified', 'simplify')
    def simplification(self, **defaults_config):
        '''
        Equat this Lambda with a form in which the body has been
        simplified.
        '''
        from proveit.logic import Equals
        inner_assumptions = \
            [assumption for assumption in defaults.assumptions if
             free_vars(assumption).isdisjoint(self.parameter_vars)]
        body_simplification = self.body.simplification(
                assumptions=inner_assumptions)
        if body_simplification == self.body:
            # No simplification.
            return Equals(self, self).conclude_via_reflexivity()
        return self.substitution(body_simplification.generalize(
                self.parameters), auto_simplify=False)

    def compose(self, lambda2):
        '''
        Given some x -> f(x) for self (lambda1) and y -> g(y) for lambda2,
        return x -> f(g(x)).  Also works with multiple parameters:
        x1, x2, ..., xn -> f(x1, x2, ..., xn)  for lambda 1 and
        y1, y2, ..., yn -> g1(y1, y2, ..., yn),
        y1, y2, ..., yn -> g2(y1, y2, ..., yn),
        ...
        y1, y2, ..., yn -> gn(y1, y2, ..., yn) for lambda2 returns
        x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), g2(x1, x2, ..., xn), ..., gn(x1, x2, ..., xn)).
        '''
        with defaults.temporary() as temp_defaults:
            # Don't auto-simplify anything when creating the composed
            # map.
            temp_defaults.auto_simplify = False
            lambda1 = self
            if is_single(lambda1.parameters):
                if not is_single(lambda2.parameters):
                    raise TypeError(
                        "lambda2 may only take 1 parameter if lambda1 "
                        "takes only 1 parameter")
                # g(x)
                relabeled_expr2 = lambda2.body.basic_replaced(
                    {lambda2.parameters[0]: lambda1.parameters[0]})
                # x -> f(g(x))
                new_body = lambda1.body.basic_replaced(
                        {lambda1.parameters[0]: relabeled_expr2})
                return Lambda(lambda1.parameters[0], new_body)
                              
            else:
                if len(lambda2) != lambda1.parameters.num_entries():
                    raise TypeError(
                        "Must supply a list of lambda2s with the same "
                        "length as the number of lambda1 parameters")
                relabeled_expr2s = []
                for lambda2elem in lambda2:
                    if (lambda2elem.parameters.num_entries() != 
                            lambda1.parameters.num_entries()):
                        raise TypeError(
                            "Each lambda2 must have the same number of "
                            "parameters as lambda1")
                    # gi(x1, x2, ..., xn)
                    param_repl_map = {
                        param2: param1 for param1,
                        param2 in zip(
                            lambda1.parameters,
                            lambda2elem.parameters)}
                    relabeled_expr2s.append(
                        lambda2elem.body.basic_replaced(param_repl_map))
                # x1, x2, ..., xn -> f(g1(x1, x2, ..., xn), 
                #                      g2(x1, x2, ..., xn), ...,
                #                      gn(x1, x2, ..., xn)).
                lambda1_expr_sub_map = {
                    param1: relabeled_expr2 for param1,
                    relabeled_expr2 in zip(
                        lambda1.parameters,
                        relabeled_expr2s)}
                return Lambda(lambda1.parameters,
                              lambda1.body.basic_replaced(lambda1_expr_sub_map))
    
    @equality_prover('substituted', 'substitute')
    def substitution(self, universal_eq, **defaults_config):
        '''
        Equate this Lambda, 
        x_1, ..., x_n -> f(x_1, ..., x_n) if Q(x_1, ..., x_n),
        with one that substitutes the body given some universal_eq:
            forall_{x_1, ..., x_n | Q(x_1, ..., x_n)} 
                f(x_1, ..., x_n) = g(x_1, ..., x_n).
        Derive and return the following type of equality assuming 
        universal_eq:
        x_1, ..., x_n -> f(x_1, ..., x_n) if Q(x_1, ..., x_n)
          = x_1, ..., x_n -> g(x_1, ..., x_n) if Q(x_1, ..., x_n).
        
        The Q conditional need not be present.
        '''
        from proveit import Conditional, Judgment
        from proveit import a, b, c, i, f, g, Q
        from proveit.logic import Forall, Equals
        from proveit.core_expr_types.lambda_maps import (
                lambda_substitution, general_lambda_substitution)
        if isinstance(universal_eq, Judgment):
            universal_eq = universal_eq.expr
        if not isinstance(universal_eq, Forall):
            raise TypeError(
                    "'universal_eq' must be a forall expression, got %s", 
                    universal_eq)
        if not isinstance(universal_eq.instance_expr, Equals):
            raise TypeError(
                    "'universal_eq' expected to be of a universally "
                    "quantified equality, got %s", universal_eq)
        equality = universal_eq.instance_expr
        _a = universal_eq.instance_params
        _b = _c = self.parameters
        _i = _b.num_elements()
        
        thm = lambda_substitution
        if hasattr(universal_eq, 'condition'):
            # use general lambda substitution.
            if not isinstance(self.body, Conditional):
                raise ValueError(
                    "'universal_eq' has conditions but this Lambda "
                    "does not have a conditional body")
            thm = general_lambda_substitution
            _f = Lambda(self.parameters, self.body.value)
        else:
            _f = Lambda(self.parameters, self.body)
        lhs_map = Lambda(universal_eq.instance_params, equality.lhs)
        rhs_map = Lambda(universal_eq.instance_params, equality.rhs)
        if _f == lhs_map:
            _g = rhs_map
        elif _f == rhs_map:
            _g = lhs_map
        else:
            raise ValueError(
                    "%s not valid as the 'universal_eq' argument for "
                    "the call to 'substitution' on %s: %s not equal "
                    "to %s or %s"%(universal_eq, self, _f, lhs_map, rhs_map))
        if thm == general_lambda_substitution:
            _Q = Lambda(self.parameters, self.body.condition)
            return thm.instantiate(
                    {i: _i, f: _f, g: _g, Q: _Q, 
                    a: _a, b: _b, c: _c},
                    preserve_expr=universal_eq).derive_consequent()
        else:
            return thm.instantiate(
                    {i: _i, f: _f, g: _g, 
                     a: _a, b: _b, c: _c},
                     preserve_expr=universal_eq).derive_consequent()


    @prover
    def _deduce_canonically_equal(self, rhs, **defaults_config):
        '''
        Prove the equality of Lambda expressions that have the same 
        canonical form.  This requires both side of
        the equality to have the same canonically labeled parameters
        and condition.
        '''
        from proveit import Conditional
        from proveit.logic import Forall, Equals
        lhs = self
        assert isinstance(rhs, Lambda), (
                "Shouldn't call _deduce_canonically_equal if the sides of "
                "the equality don't have the same canonical form and the "
                "canonical form of a Lambda is a Lambda")
        lhs_relabeled = lhs.canonically_labeled()
        rhs_relabeled = rhs.canonically_labeled()
        if (lhs_relabeled.parameters != rhs_relabeled.parameters):
            raise NotImplementedError(
                    "Lambda._deduce_canonically_equal requires the "
                    "canonically labeled parameters to be the same on "
                    "both sides (the only way this should be an issue if "
                    "they have the same canonical form is if they are "
                    "using dummy variables internally)")
        lhs_body = lhs_relabeled.body
        rhs_body = rhs_relabeled.body
        lhs_has_condition = isinstance(lhs_body, Conditional)
        rhs_has_condition = isinstance(rhs_body, Conditional)
        rhs_condition = None
        if lhs_has_condition or rhs_has_condition:
            assert lhs_has_condition == rhs_has_condition, (
                "Shouldn't call _deduce_canonically_equal if the sides "
                "of the equality don't have the same canonical form and the "
                "canonical form of a Conditional is a Conditional.")
            condition = lhs_body.condition
            rhs_condition = rhs_body.condition
            universal_eq = Forall(lhs_relabeled.parameters, 
                              Equals(lhs_body.value, rhs_body.value),
                              condition=condition)
        else:
            universal_eq = Forall(lhs_relabeled.parameters, 
                                  Equals(lhs_body, rhs_body))
        if lhs_has_condition and rhs_condition != condition:
            substitution = lhs_relabeled.substitution(
                    universal_eq, auto_simplify=False)
            # substitute the condition
            substitution= substitution.inner_expr().rhs.body.substitute_condition(
                    Equals(condition, rhs_condition))
            return substitution
        return self.substitution(universal_eq)
    


    def global_repl(master_expr, sub_expr, assumptions=USE_DEFAULTS):
        '''
        Returns the Lambda map for replacing the given sub-Expression
        everywhere that it occurs in the master Expression.

        When replacing an ExprTuple of operands, we will return a
        lambda expression with a range of parameters for replacing the
        operands individually.
        For example,
            master_expr : a + b + c
            sub_expr : (a, b, c)
            will return something equal to
                (a_1, ..., a_3) -> a_1 + ... + a_3

        'assumptions' may be required for computing the number of
        operands (which may contain ranges themselves) in this latter
        process.
        '''
        from proveit import ExprTuple, Operation

        with defaults.temporary() as temp_defaults:
            # Don't auto-simplify anything when creating our lambda
            # map.
            temp_defaults.auto_simplify = False
            if assumptions is not USE_DEFAULTS:
                temp_defaults.assumptions = assumptions
            if isinstance(sub_expr, ExprTuple):
                # If we are replacing an ExprTuple which are operands
                # that transform to a single operand, we need to instead
                # use a multi-parameter map.
                for inner_expr in traverse_inner_expressions(master_expr):
                    if (isinstance(inner_expr, Operation) and
                            inner_expr.operands == sub_expr):
                        # We should use a multi-parameter map
                        from proveit import safe_dummy_var, var_range
                        from proveit.numbers import one
                        n = sub_expr.num_elements()
                        parameters = ExprTuple(
                                var_range(safe_dummy_var(master_expr),
                                          one, n))
                        body = master_expr.basic_replaced(
                                {sub_expr: parameters})
                        return Lambda(parameters, body)

            # Just make a single parameter replacement map.
            lambda_param = master_expr.safe_dummy_var()
            return Lambda(lambda_param, master_expr.basic_replaced(
                {sub_expr: lambda_param}))

    @staticmethod
    def _free_var_ranges_static(parameters, parameter_vars, body,
                                exclusions=None):
        '''
        Static method version of _free_var_ranges.
        '''
        forms_dict = dict()
        for expr in (parameters, body):
            forms_dict.update(expr._free_var_ranges(
                exclusions=exclusions))
        for param_var in parameter_vars:
            # A lambda parameter variable effectively masks all
            # occurrences of that variable (this is enforced during
            # relabling/instantiation where we ensure that the
            # lambda parameter range covers the occurrences being
            # replaced.
            forms_dict.pop(param_var, None)
        return forms_dict

    def _free_var_ranges(self, exclusions=None):
        '''
        Return the dictionary mapping Variables to forms w.r.t. ranges
        of indices (or solo) in which the variable occurs as free
        (not within a lambda map that parameterizes the base variable).        
        Examples of "forms":
            x
            x_i
            x_1, ..., x_n
            x_{i, 1}, ..., x_{i, n_i}
            x_{1, 1}, ..., x_{1, n_1}, ......, x_{m, 1}, ..., x_{m, n_m}
        '''
        forms_dict = dict()
        if exclusions is not None and self in exclusions:
            return forms_dict  # this is excluded
        return Lambda._free_var_ranges_static(
            self.parameters, self.parameter_vars, self.body,
            exclusions=exclusions)

    def _contained_parameter_vars(self):
        '''
        Return all of the Variables of this Expression that
        are parameter variables of a contained Lambda.
        '''
        return self.parameter_var_set.union(
                self.body._contained_parameter_vars())


def extract_complete_param_replacements(parameters, parameter_vars, body,
                                        operands, 
                                        param_to_num_operand_entries,
                                        requirements, repl_map):
    '''
    Match all operands with parameters in order by checking
    tuple lengths.  Add a repl_map entry to map each
    parameter entry (or ExprTuple-wrapped entry) to corresponding
    operand(s) (ExprTuple-wrapped as appropriate).
    '''
    operands_iter = iter(operands)
    try:
        extract_param_replacements(parameters, parameter_vars,
                                   operands_iter, 
                                   param_to_num_operand_entries,
                                   requirements, repl_map, 
                                   is_complete=True)
    except ValueError as e:
        raise LambdaApplicationError(
            parameters, body, operands, [], str(e))

    # Make sure all of the operands were consumed.
    try:
        next(operands_iter)
        # All operands were not consumed.
        raise LambdaApplicationError(parameters, body,
                                     operands, [],
                                     "Too many arguments")
    except StopIteration:
        pass  # Good.  All operands were consumed.


def extract_param_replacements(parameters, parameter_vars,
                               operands_iter, param_to_num_operand_entries,
                               requirements, repl_map, is_complete=False):
    '''
    Match the operands, as needed, with parameters in order by checking
    tuple lengths.  If provided (not None), param_to_num_operand_entries
    indicates how many operand entries should correspond with each
    parameter to speed making matches and disambiguate which parameter
    empty ranges belong to.  Add a repl_map entry to map each
    parameter entry (or ExprTuple-wrapped entry) to corresponding
    operand(s) (ExprTuple-wrapped as appropriate).
    '''
    from proveit import (ExprTuple, ExprRange, ProofFailure,
                         extract_var_tuple_indices)
    from proveit.logic import Equals
    from proveit.core_expr_types import Len
    # Loop through each parameter entry and match it with corresponding
    # operand(s).  Singular parameter entries match with singular
    # operand entries.  ExprRange parameter entries match with
    # one or more operand entries which match in element-wise length
    # For example, (x_1, ..., x_n, y) has an element-wise lenght of
    # n+1.
    try:
        for parameter, param_var in zip(parameters, parameter_vars):
            if isinstance(parameter, ExprRange):
                from proveit.numbers import zero, one

                # This is a parameter range which corresponds with
                # one or more operand entries in order to match the
                # element-wise length.
                param_indices = extract_var_tuple_indices(
                    ExprTuple(parameter))
                param_len = Len(param_indices)
                
                # If we know how many operand entries are associated
                # with the parameter, we can avoid work and possibly
                # avoid ambiguity when assigning empty ranges.
                if param_to_num_operand_entries is not None:
                    num_operand_entries = (
                        param_to_num_operand_entries[parameter])
                    param_operands = [next(operands_iter) for _ 
                                      in range(num_operand_entries)]
                    param_tuple = ExprTuple(parameter)
                    param_operands_tuple = ExprTuple(*param_operands)
                    param_operands_len = Len(param_operands_tuple)
                    repl_map[param_var] = {param_tuple}
                    repl_map[param_tuple] = param_operands_tuple
                    if param_operands_len==param_len:
                        # Trivial length requirement
                        continue
                    len_req = Equals(param_operands_len, param_len)
                    requirements.append(len_req.prove())
                    continue
                
                try:
                    # Maybe a known integer value for param_len.
                    int_param_len = parameter.literal_int_extent()
                except ValueError:
                    # Unknown integer value for param_len.
                    int_param_len = None
                # Collect enough operands to match the length of
                # the range of parameters.
                param_operands = []
                # To the extent they are known, track the minimum
                # and maximum number of param-operand elements.
                min_int_param_operands_len = 0
                max_int_param_operands_len = 0
                final_param = is_complete and (parameters[-1] == parameter)
                while True:
                    param_operands_tuple = ExprTuple(*param_operands)
                    param_operands_len = Len(param_operands_tuple)
                    len_req = Equals(param_operands_len, param_len)
                    # Check for obvious failure of len_req
                    if (int_param_len is not None and
                            min_int_param_operands_len > int_param_len):
                        # No good. Too many arguments for parameter.
                        raise ValueError(
                            "Too many arguments, %s, for parameter"
                            " %s." % (param_operands, parameter))
                    elif (not final_param and 
                          (max_int_param_operands_len is None or
                           int_param_len is None or
                           max_int_param_operands_len == int_param_len)):
                        # A possible match to check.
                        if not len_req.proven():
                            try:
                                len_req.lhs.deduce_equal(len_req.rhs)
                                assert len_req.proven()
                            except ProofFailure:
                                pass
                        if len_req.proven():
                            requirements.append(len_req.prove())
                            break  # we have a match
                    try:
                        operand_entry = next(operands_iter)
                    except StopIteration:
                        if len_req.proven():
                            # Length requirement already satisfied.
                            requirements.append(len_req.prove())
                            break
                        try:
                            # Try to prove len_req via 'deduce_equal'
                            len_req.lhs.deduce_equal(len_req.rhs)
                            requirements.append(len_req.prove())
                        except ProofFailure as e:
                            raise ValueError(
                                "Failed to prove operand length "
                                "requirement, %s: %s" 
                                % (len_req, str(e)))
                        break # No more operands
                    # Update min/max number of param-operand
                    # elements.
                    if isinstance(operand_entry, ExprRange):
                        try:
                            # Maybe a known integer ExprRange length.
                            entry_len = operand_entry.literal_int_extent()
                            min_int_param_operands_len += entry_len
                            if max_int_param_operands_len is not None:
                                max_int_param_operands_len += entry_len
                        except ValueError:
                            # Unnown ExprRange length, but >= 0.
                            max_int_param_operands_len = None
                    else:
                        # Single element operand.
                        min_int_param_operands_len += 1
                        if max_int_param_operands_len is not None:
                            max_int_param_operands_len += 1
                    # Append this operand entry to the param_operands.
                    param_operands.append(operand_entry)
                        
                # For the parameter range replacement, we map the
                # parameter variable to a set of parameter range
                # tuples (e.g., x : {(x_i, ..., x_n)}) to indicate
                # the index range and then map that iteration tuple
                # to the actual operands to be replaced.
                param_tuple = ExprTuple(parameter)
                repl_map[param_var] = {param_tuple}
                repl_map[param_tuple] = ExprTuple(*param_operands)
            else:
                # This is a singular parameter which should match
                # with a singular operand or range(s) with known
                # length summing up to 1 (may have zero length
                # ranges).
                operand = next(operands_iter)
                if isinstance(operand, ExprRange):
                    # Rangle lengths must be known values and sum
                    # to 1.
                    from proveit.numbers import zero, one
                    while True:
                        operand_len_evaluation = \
                            Len(operand).evaluation()
                        requirements.append(operand_len_evaluation)
                        operand_len_val = operand_len_evaluation.rhs
                        if operand_len_val == one:
                            # We know the length of this ExprRange is 
                            # one, so just use the first entry as the 
                            # only entry.  (This should not usually
                            # come up since singular ExprRanges are
                            # automatically reduced when the start and
                            # end are the same).
                            operand = operand.body.basic_replaced(
                                    {operand.parameter: operand.true_start_index})
                            break  # Good to go.
                        elif operand_len_val == zero:
                            # Keep going until we get a length
                            # of 1.
                            operand = next(operands_iter)
                        else:
                            # No good.
                            raise ValueError(
                                "Parameter/argument length "
                                "mismatch 1 vs %s"
                                % operand_len_evaluation.rhs)
                        if not isinstance(operand, ExprRange):
                            # We have our singular operand to match
                            # a singular parameter.
                            break
                repl_map[parameter] = operand
    except StopIteration:
        raise ValueError("Parameter/argument length mismatch "
                         "or unproven length equality for "
                         "correspondence with %s." % str(parameter))

class ParameterCollisionError(Exception):
    def __init__(self, parameters, main_msg):
        self.parameters = parameters
        self.main_msg = main_msg

    def __str__(self):
        return ("%s.  %s does not satisfy this criterion."
                % (self.main_msg, self.parameters))

class ParameterMaskingError(Exception):
    '''
    Lambda's are not allowed to mask a range of parameters while the
    body contains parameters outside of this range (partial masking).
    We only catch this when it is easy/convenient or when it really 
    matters.  We catch it for a simple indexed parameter (effectively
    a singular range) while generating the canonical form or while
    instantiating/relabeling (as an ImproperReplacement).
    '''
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class ParameterRelabelingError(Exception):
    def __init__(self, expr, relabel_map):
        self.expr = expr
        self.relabel_map = relabel_map

    def __str__(self):
        return "Invalid relabeling of %s: %s"%(self.expr, self.relabel_map)

class LambdaApplicationError(Exception):
    def __init__(self, parameters, body, operands,
                 equiv_alt_expansions, extra_msg):
        from proveit._core_.expression.composite.composite import \
            composite_expression
        self.parameters = composite_expression(parameters)
        self.body = body
        self.operands = operands
        self.assumptions = defaults.assumptions
        self.equiv_alt_expansions = equiv_alt_expansions
        self.extra_msg = extra_msg

    def __str__(self):
        assumption_str = ''
        equiv_alt_expansions_str = ''
        if len(self.assumptions) > 0:
            assumption_str = ' assuming %s' % str(self.assumptions)
        if (self.equiv_alt_expansions is not None and
                len(self.equiv_alt_expansions) > 0):
            equiv_alt_expansions_str = (
                " using equivalent alternate expansions of %s"
                % self.equiv_alt_expansions)
        return ("Failure to apply %s to %s%s%s:\n%s"
                % (Lambda._string(self.parameters, self.body),
                   self.operands, equiv_alt_expansions_str,
                   assumption_str, self.extra_msg))


class ArgumentExtractionError(Exception):
    def __init__(self, specifics):
        self.specifics = specifics

    def __str__(self):
        return (
            "Cannot extract argument(s); mapped_expr does not match this Lambda "
            "expression: " + self.specifics)

