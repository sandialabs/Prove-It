from .expr import Expression, free_vars
from .operation import Operation, Function
from .lambda_expr import Lambda
from .composite import ExprTuple, Composite, NamedExprs, composite_expression
from proveit._core_.defaults import defaults, USE_DEFAULTS
import inspect


class InnerExpr:
    '''
    Represents an "inner" sub-expression of a particular "top_level"
    Expression or Judgment.  The inner_expr method of the Expression
    (or Judgment) class will start an InnerExpr with that particular
    expression (or judgment) as the top-level.  This acts as an
    expression wrapper, starting at the top-level but can "descend" to
    any sub-expression (or the 'assumptions' in the Judgment case)
    via accessing sub-expression attributes (or 'assumptions').
    This will allow us to manipute the inner expression in the
    theory of the containing Expression/Judgment object.  One can
    change the style of the inner expression or replace it with an
    equivalent form.

    Equivalence methods may be registered via
    InnerExpr.register_equivalence_method(...).
    Registering an equivalence method allows one to directly
    replace the inner expression with a form that is produced
    by calling the equivalence method.  Examples are:
        evaluation, simplification, commutation, association, etc.
    When registering such a method, a noun form (as above), a
    past tense form, and an action form are to be simplied
    (e.g., 'evaluation', 'evaluated', and 'evaluate').  Calling
    the first version (e.g., 'evaluation') will produce a proven
    equality between the original top-level expression and a form
    in which the inner expression is replaced with its new form.
    Calling the second version (e.g., 'evaluated') will prove
    the equality as before but simply return the right side (the
    new form of the top-level, with the inner expression replaced).
    The last version (e.g., 'evaluate') is to be applied to
    proven (or easilty provable) top-level expressions and will
    yield the proven top-level expression (under given assumptions)
    with the inner expression replaced by its equivalent form.

    For example, let "expr = [((a - 1) + b + (a - 1)/d) < e]", and let
    "inner_expr = expr.innter_expr().lhs.terms[2].numerator".  Then

    1. inner_expr.repl_lambda() will return
       _x_ -> [((a - 1) + b + _x_/d) < e],
       replacing the particular inner expression.
       (note that the second "a - 1" is singled out, distinct from
       the first "a - 1" because the subexpr object tracks the
       sub-expression by "location").
    2. inner_expr.with_subtraction_at([]) will return an
       expression that is the same but with an altered style for the
       inner exrpession part:
           [((a - 1) + b + (a + (-1))/d) < e]
       The InnerExpr class looks specifically for attributes of the
       inner expression class that start with 'with' and assumes
       they function to alter the style.
    3. inner_expr.commutation(0, 1) would return:
           |- [((a - 1) + b + (a - 1)/d) < e]
              = [((a - 1) + b + (-1 + a)/d) < e]
       assuming 'a' is known to be a number.
    4. inner_expr.commuted(0, 1) would return:
           [((a - 1) + b + (-1 + a)/d) < e]
       assuming 'a' is known to be a number.  It will prove #3 along the way.
    5. inner_expr.commute(0, 1) would return
           |-  ((a - 1) + b + (-1 + a)/d) < e
       assuming the original expr may be proven via automation and
       'a' is known to be a number.
    6. inner_expr.substitution(a + 1 - 2) would return
           |- [((a - 1) + b + (a - 1)/d) < e]
              = [((a - 1) + b + (a + 1 - 2)/d) < e]
    7. inner_expr.substitute(a + 1 - 2) would return
           |- [((a - 1) + b + (a + 1 - 2)/d) < e]

    In addition, the InnerExpr class has 'simplify_operands' and
    'evaluate_operands' methods for effecting 'simplify' or 'evaluate'
    (respectively) on all of the operands of the inner expression.

    '''

    def __init__(self, top_level, _inner_expr_path=tuple(),
                 assumptions=USE_DEFAULTS):
        '''
        Create an InnerExpr with the given top-level Expression
        or Judgment.  When getting an item or attribute
        that corresponds with an item/attribute of the current
        inner expression, a new InnerExpr is generated, extending the
        path from the top level to the corresponding inner expression.
        The _inner_expr_path is used internally for this purpose.

        Assumptions are only needed when a slice of an ExprTuple
        will be taken and getting the number of elements of
        the slice (ExprTuple.length) is necessary to when calling
        repl_lambda().
        '''
        from proveit import Judgment
        self.inner_expr_path = tuple(_inner_expr_path)
        self.expr_hierarchy = [top_level]
        self.assumptions = assumptions
        # list all of the lambda expression parameters encountered
        # along the way from the top-level expression to the inner
        # expression.
        self.parameters = []
        expr = self.expr_hierarchy[0]
        for idx in self.inner_expr_path:
            if isinstance(expr, Judgment) and idx == -1:
                # The top level may actually be a Judgment rather
                # than an expression.
                # idx==-1 corresponds to the assumptions of the
                # Judgment.
                kt = expr
                expr = kt.assumptions
            else:
                if isinstance(expr, Lambda) and idx == expr.num_sub_expr() - 1:
                    # while descending into a lambda expression body, we
                    # pick up the lambda parameters.
                    self.parameters.extend(expr.parameters.entries)
                expr = expr.sub_expr(idx)
                if isinstance(expr, tuple):
                    # A slice `idx` will yield a tuple sub expression.
                    # Convert it to an ExprTuple
                    expr = ExprTuple(*expr)
            self.expr_hierarchy.append(expr)

    def __eq__(self, other):
        return (self.inner_expr_path == other.inner_expr_path and
                self.expr_hierarchy == other.expr_hierarchy)

    def __getitem__(self, key):
        '''
        If the currently mapped sub-Expression of the SubExprRepl
        is a Composite, accessing an item corresponding to an item
        of this Composite will return the SubExprRepl with the extended
        path to this item.
        '''
        cur_inner_expr = self.expr_hierarchy[-1]
        if isinstance(cur_inner_expr, ExprTuple):
            # For an ExprTuple, the item key is either the index of the
            # sub-Expression or a slice (in which case the replacement map
            # has multiple parameters).
            if isinstance(key, int) and key < 0:
                key = cur_inner_expr.num_entries() + key
            if isinstance(key, slice):
                if key.step is not None and key.step != 1:
                    raise ValueError("When using a slice for an InnerExpr, the"
                                     " step must be 1, not %d" % key.step)
            return InnerExpr(self.expr_hierarchy[0], self.inner_expr_path + (key,),
                             assumptions=self.assumptions)
        elif isinstance(cur_inner_expr, Composite):
            # For NamedExprs, the key is the key of its dictionary.
            # The sub-Expressions are in the order of the keys.
            keys = cur_inner_expr.keys()
            return InnerExpr(self.expr_hierarchy[0],
                             self.inner_expr_path + [keys.index(key)],
                             assumptions=self.assumptions)
        raise KeyError("The current sub-Expression is not a Composite.")

    def _get_attr_as_inner_expr(self, cur_depth, attr, attr_expr):
        '''
        Try to find a deeper inner expression that corresponds with the
        attribute (attr) of the expression at the given current depth
        (cur_depth) along the self InnerExpr.  It will perform a
        recursive breadth-first search until it finds a match, making
        sure the deeper inner expression corresponds with that specific
        attribute (not just happening to be the same sub-expression that
        could occur multiple places).
        '''
        from proveit._core_.judgment import Judgment
        top_level_expr = self.expr_hierarchy[0]
        cur_inner_expr = self.expr_hierarchy[-1]
        if isinstance(cur_inner_expr, Judgment):
            cur_inner_expr = cur_inner_expr.expr
        inner_subs = list(cur_inner_expr.sub_expr_iter())
        # See if any of the sub-expressions are a match.
        for i, inner_sub in enumerate(inner_subs):
            if inner_sub == attr_expr:
                # To make sure that the deeper inner expression does
                # correspond with the specific attribute, form the
                # corresponding replacement map and make sure its
                # parameter is accessed by that attribute.
                deeper_inner_expr = InnerExpr(top_level_expr,
                                              self.inner_expr_path + (i,),
                                              assumptions=self.assumptions)
                if (isinstance(cur_inner_expr, Operation) 
                        and cur_inner_expr.operands == attr_expr):
                    # The 'operands' attribute of an Operation is a
                    # special case.  Take the full slice and we don't
                    # need to check it.
                    return deeper_inner_expr[:]
                repl_lambda = deeper_inner_expr.repl_lambda()
                sub_expr = repl_lambda .body
                for j in self.inner_expr_path[:cur_depth]:
                    if isinstance(sub_expr, ExprTuple):
                        sub_expr = sub_expr[j]
                    else:
                        sub_expr = sub_expr.sub_expr(j)
                fvars = free_vars(
                    composite_expression(getattr(sub_expr,attr)),
                    err_inclusively=False)
                if repl_lambda.parameter_var_set.issubset(fvars):
                    return deeper_inner_expr
        # No match found at this depth -- let's continue to the next
        # depth
        for i, inner_sub in enumerate(inner_subs):
            inner_expr = InnerExpr(self.expr_hierarchy[0],
                                   self.inner_expr_path + (i,),
                                   assumptions=self.assumptions)
            inner_expr = inner_expr._get_attr_as_inner_expr(
                    cur_depth, attr, attr_expr)
            if inner_expr is not None:
                return inner_expr
        return None  # no match found down to the maximum depth

    def __getattr__(self, attr):
        '''
        See if the attribute is accessing a deeper inner expression of
        the represented inner expression.  If so, return the InnerExpr
        with the extended path to the sub-expression.
        For methods of the inner expression that begin as 'with',
        generate a method that returns a new version of the top-level
        expression with the inner expression changed according to its
        'with' method.
        '''
        from proveit import OperationOverInstances
        cur_inner_expr = self.expr_hierarchy[-1]
        if hasattr(cur_inner_expr.__class__, '_equiv_method_%s_' % attr):
            equiv_method_type, equiv_method_name = \
                getattr(cur_inner_expr.__class__, '_equiv_method_%s_' % attr)
            equiv_method = getattr(cur_inner_expr, equiv_method_name)
            # Find out which argument is the 'assumptions' argument:
            try:
                argspec = inspect.getfullargspec(equiv_method)
                assumptions_index = argspec.args.index('assumptions') - 1
            except ValueError:
                raise Exception(
                    "Expecting method, %s, to have 'assumptions' argument." %
                    str(equiv_method))
            repl_lambda = self.repl_lambda()
            if (isinstance(cur_inner_expr, ExprTuple)
                    and len(self.expr_hierarchy) > 2
                    and isinstance(self.expr_hierarchy[-2], Operation)):
                # When replace operands of an operation, we need a
                # a repl_lambda with a range of parameters.
                repl_lambda = self[:].repl_lambda()

            def inner_equiv(*args, **kwargs):
                if 'assumptions' in kwargs:
                    assumptions = kwargs['assumptions']
                elif len(args) > assumptions_index:
                    assumptions = args[assumptions_index]
                else:
                    assumptions = USE_DEFAULTS
                equivalence = equiv_method(*args, **kwargs)
                # We need to disable the auto-reduction as we
                # are making this substitution to ensure we do not
                # much with anything other than the specific
                # "inner expression".
                was_auto_reduce_enabled = defaults.auto_reduce
                try:
                    defaults.auto_reduce = False
                    if equiv_method_type == 'equiv':
                        return equivalence.substitution(
                            repl_lambda, assumptions)
                    elif equiv_method_type == 'rhs':
                        return equivalence.substitution(
                            repl_lambda, assumptions).rhs
                    elif equiv_method_type == 'action':
                        return equivalence.sub_right_side_into(
                            repl_lambda, assumptions)
                finally:
                    # Restore the 'auto_reduction' default.
                    defaults.auto_reduce = was_auto_reduce_enabled
            if equiv_method_type == 'equiv':
                inner_equiv.__doc__ = "Generate an equivalence of the top-level expression with a new form by replacing the inner expression via '%s'." % equiv_method_name
            elif equiv_method_type == 'rhs':
                inner_equiv.__doc__ = "Return an equivalent form of the top-level judgment by replacing the inner expression via '%s'." % equiv_method_name
            elif equiv_method_type == 'action':
                inner_equiv.__doc__ = "Derive an equivalent form of the top-level judgment by replacing the inner expression via '%s'." % equiv_method_name
            else:
                raise ValueError(
                    "Unexpected 'equivalence method' type: %s." %
                    equiv_method_type)
            inner_equiv.__name__ = attr
            return inner_equiv

        if attr == 'relabel':
            attr = 'relabeled'
        if (attr == 'relabeled' and
                isinstance(cur_inner_expr, OperationOverInstances)):
            # When calling 'relabeled' on an OperationOverInstances
            # inner expression, we need to go one level deeper to
            # the lambda expression.
            cur_inner_expr = cur_inner_expr.operand
        if not hasattr(cur_inner_expr, attr):
            raise AttributeError(
                "No attribute '%s' in '%s' or '%s'" %
                (attr, self.__class__, cur_inner_expr.__class__))

        inner_attr_val = getattr(cur_inner_expr, attr)
        if isinstance(inner_attr_val, Expression):
            # The attribute is addressing a sub-Expression of the current inner Expression
            # and may be a sub-sub-Expression (or a member of sub-sub-Expression composite);
            # if so, return the SubExprRepl extended to the sub-sub-Expression.
            inner_expr = self._get_attr_as_inner_expr(
                len(self.inner_expr_path), attr, inner_attr_val)
            if inner_expr is not None:
                return inner_expr
        elif attr == 'relabeled' or attr[:4] == 'with':
            def revise_inner_expr(*args, **kwargs):
                # call the 'with...' method on the inner expression:
                expr = getattr(cur_inner_expr, attr)(*args, **kwargs)
                # Rebuild the expression (or Judgment) with the
                # inner expression replaced.
                return self._rebuild(expr)
            '''
                #getattr(cur_sub_expr, attr)(*args, **kwargs)  # this will also revise the styles of all parents recursively

                return self.expr_hierarchy[0] # return the top-level expression
            '''
            return revise_inner_expr

        # not a sub-expression, so just return the attribute for the actual
        # Expression object of the sub-expression
        return getattr(cur_inner_expr, attr)

    @staticmethod
    def register_equivalence_method(
            expr_class,
            equiv_method,
            past_tense_name,
            action_name):
        '''
        Register a method of an expression class that is used to derive and return (as a Judgment)
        the equivalence of that expression on the left side with a new form on the right side.
        (e.g., 'simplification', 'evaluation', 'commutation', 'association').
        In addition to the expression class and the method (as a name or function object), also
        provide the "past-tense" form of the name for deriving the equivalence and returning
        the right side, and provide the "action" form of the name that may be used to make
        the replacement directly within a Judgment to produce a revised Judgment.
        The "past-tense" version will be added automatically as a method to the given expression
        class with an appropriate doc string.
        '''
        if not isinstance(equiv_method, str):
            # can be a string or a function:
            equiv_method = equiv_method.__name__
        if not hasattr(expr_class, equiv_method):
            raise Exception(
                "Must have '%s' method defined in class '%s' in order to register it as an equivalence method in InnerExpr." %
                (equiv_method, str(expr_class)))

        # Store information in the Expression class that will enable calling
        # InnerExpr methods when an expression of that type
        # is the inner expression for generating equivalences or performing
        # in-place replacements.
        setattr(
            expr_class, '_equiv_method_%s_' %
            equiv_method, ('equiv', equiv_method))
        setattr(
            expr_class, '_equiv_method_%s_' %
            past_tense_name, ('rhs', equiv_method))
        setattr(
            expr_class, '_equiv_method_%s_' %
            action_name, ('action', equiv_method))

        # Automatically create the "paste-tense" equivalence method for the
        # expression class which returns the right side.
        if hasattr(expr_class, past_tense_name):
            raise Exception(
                "Should not manually define '%s' in class '%s'.  This 'past-tense' equivalence method will be generated automatically by registering it in InnerExpr." %
                (past_tense_name, str(expr_class)))

        def equiv_rhs(expr, *args, **kwargs):
            return getattr(expr, equiv_method)(*args, **kwargs).rhs
        equiv_rhs.__name__ = past_tense_name
        equiv_rhs.__doc__ = "Return an equivalent form of this expression derived via '%s'." % equiv_method
        setattr(expr_class, past_tense_name, equiv_rhs)

    def repl_lambda(self):
        '''
        Returns the lambda function/map that would replace this
        particular inner expression within the top-level expression.
        '''
        from proveit import Judgment, var_range
        # build the lambda expression, starting with the lambda
        # parameter and working up the hierarchy.
        top_level = self.expr_hierarchy[0]
        if isinstance(top_level, Judgment):
            top_level_expr = top_level.expr
        else:
            top_level_expr = top_level

        cur_sub_expr = self.expr_hierarchy[-1]
        cur_idx = self.inner_expr_path[-1] if len(
            self.inner_expr_path) > 0 else None

        if isinstance(cur_idx, slice):
            # When there is a slice of an ExprTuple at the bottom level,
            # we will map an iteration of parameters as the filler for
            # the slice.
            from proveit.numbers import one
            assert isinstance(cur_sub_expr, ExprTuple), "Unexpected type"
            parent_tuple = self.expr_hierarchy[-2]
            assert isinstance(parent_tuple, ExprTuple), "Unexpected type"
            start, stop = cur_idx.start, cur_idx.stop
            if start is None:
                start = 0
            if stop is None:
                stop = parent_tuple.num_entries()
            sub_tuple_len = cur_sub_expr.num_elements(self.assumptions)
            dummy_var = top_level_expr.safe_dummy_var()
            lambda_params = var_range(dummy_var, one, sub_tuple_len)
            lambda_body = ExprTuple(*(parent_tuple[:start].entries + (lambda_params,)
                                      + parent_tuple[stop:].entries))
            """
        elif isinstance(cur_sub_expr, Composite):
            dummy_vars = top_level_expr.safe_dummy_vars(len(cur_sub_expr))
            lambda_params = dummy_vars
            cur_sub_class = cur_sub_expr.__class__
            if self.parameters.num_entries()==0:
                lambda_body = cur_sub_class._checked_make(
                        cur_sub_expr.core_info(), cur_sub_expr.get_styles(),
                        dummy_vars)
            else:
                # The replacements should be a function of the
                # parameters encountered between the top-level
                # expression and the inner expression.
                lambda_body = cur_sub_class._checked_make(
                        cur_sub_expr.core_info(), 
                        [Function(dummy_var, self.parameters)
                         for dummy_var in dummy_vars])
            """
        else:
            lambda_params = [top_level_expr.safe_dummy_var()]
            if len(self.parameters) == 0:
                lambda_body = lambda_params[0]
            else:
                # The replacements should be a function of the
                # parameters encountered between the top-level
                # expression and the inner expression.
                lambda_body = Function(lambda_params[0], self.parameters)
        # Build the expression with replacement parameters from
        # the inside out.
        lambda_body = self._rebuild(lambda_body)
        return Lambda(lambda_params, lambda_body)

    def _rebuild(self, inner_expr_replacement):
        '''
        Rebuild the expression replacing the inner expression with the
        given 'inner_expr_replacement'.
        '''
        from proveit import Judgment
        inner_expr = inner_expr_replacement
        # Work from the inside out.
        for expr, idx in reversed(list(zip(self.expr_hierarchy,
                                           self.inner_expr_path))):
            if isinstance(idx, slice):
                continue
            if isinstance(expr, Judgment):
                if idx < 0:
                    raise ValueError("Cannot call an InnerExpr.repl_lambda "
                                     "for an inner expression of one of "
                                     "a Judgment's assumptions")
                # Convert from a Judgment to an Expression.
                expr = expr.expr
            expr_subs = tuple(expr.sub_expr_iter())
            inner_expr = expr.__class__._make(
                expr.core_info(), 
                expr_subs[:idx] + (inner_expr,) + expr_subs[idx + 1:])
        revised_expr = inner_expr
        if (isinstance(self.expr_hierarchy[0], Judgment) and
                self.expr_hierarchy[0].expr == revised_expr):
            # Make a Judgment with only the style modified.
            kt = Judgment(revised_expr, self.expr_hierarchy[0].assumptions)
            kt._addProof(self.expr_hierarchy[0].proof())
            return kt
        return revised_expr

    def substitution(self, replacement, assumptions=USE_DEFAULTS):
        '''
        Equate the top level expression with a similar expression
        with the inner expression replaced by the replacement.
        '''
        from proveit.logic import Equals
        cur_inner_expr = self.expr_hierarchy[-1]
        equality = Equals(cur_inner_expr, replacement).prove(assumptions)
        equality.substitution(self.repl_lambda(), assumptions=assumptions)

    def substitute(self, replacement, assumptions=USE_DEFAULTS):
        '''
        Substitute the replacement in place of the inner expression
        and return a new proven statement (assuming the top
        level expression is proven, or can be proven automatically).
        '''
        from proveit import x, P
        from proveit.logic import TRUE, FALSE, Equals
        from proveit.logic.equality import (
            substitute_truth, substitute_falsehood)
        cur_inner_expr = self.expr_hierarchy[-1]
        if cur_inner_expr == TRUE:
            return substitute_truth.instantiate(
                {P: self.repl_lambda(), x: replacement},
                assumptions=assumptions)
        elif cur_inner_expr == FALSE:
            return substitute_falsehood.instantiate(
                {P: self.repl_lambda(), x: replacement},
                assumptions=assumptions)
        else:
            Equals(cur_inner_expr, replacement).sub_right_side_into(
                self.repl_lambda(), assumptions=assumptions)

    def _expr_rep(self):
        '''
        Representation as NamedExprs that indicates not only the lambda
        function but the sub-Expressions that may be accessed more
        deeply.
        '''
        repl_lambda = self.repl_lambda()
        lambda_params = repl_lambda.parameters
        cur_sub_expr = self.expr_hierarchy[-1]
        # if isinstance(cur_sub_expr, Composite):
        #    sub_exprs = list(cur_sub_expr.sub_expr_iter())
        # else:
        sub_exprs = [cur_sub_expr]
        named_expr_dict = [('lambda', repl_lambda)]
        if len(self.parameters) == 0:
            named_expr_dict += [('$%s$' % lambda_param.latex(), sub_expr)
                                for lambda_param, sub_expr
                                in zip(lambda_params, sub_exprs)]
        else:
            def make_fn(lambda_param): return Function(lambda_param,
                                                       self.parameters)
            named_expr_dict += \
                [('$%s$' % make_fn(lambda_param).latex(), sub_expr)
                 for lambda_param, sub_expr in zip(lambda_params, sub_exprs)]
        return NamedExprs(named_expr_dict)

    def cur_sub_expr(self):
        return self.expr_hierarchy[-1]

    def simplify_operands(self, assumptions=USE_DEFAULTS):
        from proveit.logic import default_simplification
        return default_simplification(self, in_place=True, operands_only=True,
                                      assumptions=assumptions)

    def evaluate_operands(self, assumptions=USE_DEFAULTS):
        from proveit.logic import default_simplification
        return default_simplification(
            self, in_place=True, must_evaluate=True, operands_only=True,
            assumptions=assumptions)

    def _repr_html_(self):
        return self._expr_rep()._repr_html_()

    def __repr__(self):
        return self._expr_rep().__repr__()


# Register these generic expression equivalence methods:
InnerExpr.register_equivalence_method(
    Expression,
    'simplification',
    'simplified',
    'simplify')
InnerExpr.register_equivalence_method(
    Expression, 'evaluation', 'evaluated', 'evaluate')
