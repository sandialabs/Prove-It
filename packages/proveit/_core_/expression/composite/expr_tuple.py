import types
from .composite import Composite
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.proof import ProofFailure
from proveit._core_.defaults import USE_DEFAULTS
from proveit._core_.expression.style_options import StyleOptions


class ExprTuple(Composite, Expression):
    """
    An ExprTuple is a composite Expression composed of an ordered list
    of member Expression "entries".  The ExprTuple represents a
    mathematical tuple as an ordered collection of "elements".
    Each entry may either represent a single element or a "range"
    of elements.  An entry that is an ExprRange represents a range
    of elements.  For example,
    (a, b, x_1, ..., x_n, c, d)
    Is represented by an ExprTuple with 5 entries representing
    n+4 elements.
    """

    def __init__(self, *expressions):
        '''
        Initialize an ExprTuple from an iterable over Expression
        objects.
        '''
        from proveit._core_ import Judgment
        from .composite import single_or_composite_expression
        entries = []
        for entry in expressions:
            if isinstance(entry, Judgment):
                # Extract the Expression from the Judgment:
                entry = entry.expr
            if not isinstance(entry, Expression):
                entry = single_or_composite_expression(entry)
            assert isinstance(entry, Expression)
            entries.append(entry)
        self.entries = tuple(entries)
        Expression.__init__(self, ['ExprTuple'], self.entries)

    def style_options(self):
        options = StyleOptions(self)
        if len(self.entries) > 1:
            options.add_option(
                    name='wrap_positions',
                    description=("position(s) at which wrapping is to occur; "
                                 "'n' is after the nth comma."),
                    default = '()',
                    related_methods = ('with_wrapping_at',))
            options.add_option(
                name = 'justification',
                description = ("if any wrap positions are set, justify to the "
                               "'left', 'center', or 'right'"),
                default = 'left',
                related_methods = ('with_justification',))
        return options

    def with_wrapping_at(self, *wrap_positions):
        return self.with_styles(
            wrap_positions='(' +
            ' '.join(
                str(pos) for pos in wrap_positions) +
            ')')

    def with_justification(self, justification):
        return self.with_styles(justification=justification)

    @classmethod
    def _make(sub_class, core_info, sub_expressions):
        if sub_class != ExprTuple:
            MakeNotImplemented(sub_class)
        if len(core_info) != 1 or core_info[0] != 'ExprTuple':
            raise ValueError("Expecting ExprTuple core_info to contain "
                             "exactly one item: 'ExprTuple'")
        return ExprTuple(*sub_expressions)

    def remake_arguments(self):
        '''
        Yield the argument values or (name, value) pairs
        that could be used to recreate the ExprTuple.
        '''
        for sub_expr in self.sub_expr_iter():
            yield sub_expr

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        wrap_positions = self.wrap_positions()
        call_strs = []
        if len(wrap_positions) > 0:
            call_strs.append('with_wrapping_at(' + ','.join(str(pos)
                                                            for pos in wrap_positions) + ')')
        justification = self.get_style('justification', 'left')
        if justification != 'left':
            call_strs.append('with_justification("' + justification + '")')
        return call_strs

    def __iter__(self):
        '''
        Iterator over the entries of the list.
        Some entries may be ranges (ExprRange) that
        represent multiple elements of the list.
        '''
        return iter(self.entries)

    def __len__(self):
        raise NotImplementedError(
                "__len__ is deliberately not implement in order to avoid "
                "ambiguity.  Use num_entries or num_elements.")

    def num_entries(self):
        '''
        Return the number of entries of the list.
        Some entries may be ranges (ExprRange) that
        represent multiple elements of the list.
        '''
        return len(self.entries)

    def __getitem__(self, idx):
        '''
        Return the list entry at the ith index.
        This is a relative entry-wise index where
        entries may represent multiple elements
        via ranges (ExprRange).
        '''
        if isinstance(idx, slice):
            return ExprTuple(*self.entries[idx])
        return self.entries[idx]

    def __add__(self, other):
        '''
        Concatenate ExprTuple's together via '+' just like
        Python lists.  Actually works with any iterable
        of Expressions as the second argument.
        '''
        if isinstance(other, ExprTuple):
            return ExprTuple(*(self.entries + other.entries))
        else:
            return ExprTuple(*(self.entries + tuple(other)))

    def is_single(self):
        '''
        Return True if this has a single element that is not an
        ExprRange.
        '''
        return is_single(self)

    def is_double(self):
        '''
        Returns True if this has two elements that are not ExprRanges.
        '''
        return is_double(self)

    def contains_range(self):
        '''
        Returns true if the entry contains an ExprRange.
        '''
        from .expr_range import ExprRange
        return any(isinstance(entry, ExprRange) for entry in self.entries)
    
    def index(self, entry, start=0, stop=None):
        if stop is None:
            return self.entries.index(entry, start)
        else:
            return self.entries.index(entry, start, stop)

    def wrap_positions(self):
        '''
        Return a list of wrap positions according to the current style setting.
        Position 'n' is after the nth comma.
        '''
        if len(self.entries) < 2:
            # There can be no "wrap positions" unless there are 2 or
            # more entries.
            return [] 
        return [int(pos_str) for pos_str in self.get_style(
            'wrap_positions').strip('()').split(' ') if pos_str != '']

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(
            self,
            format_type,
            fence=True,
            sub_fence=False,
            operator_or_operators=None,
            implicit_first_operator=False,
            wrap_positions=None,
            justification=None,
            **kwargs):
        from .expr_range import ExprRange

        out_str = ''
        if len(self.entries) == 0 and fence:
            # for an empty list, show the parenthesis to show something.
            return '()'

        if wrap_positions is None:
            # Convert from a convention where position 'n' is after the nth comma to one in which the position '2n' is
            # after the nth operator (which also allow for position before
            # operators).
            wrap_positions = [2 * pos for pos in self.wrap_positions()]
        if justification is None:
            justification = self.get_style('justification', 'left')

        do_wrapping = len(wrap_positions) > 0
        if fence:
            out_str = '(' if format_type == 'string' else r'\left('
        if do_wrapping and format_type == 'latex':
            out_str += r'\begin{array}{%s} ' % justification[0]

        formatted_sub_expressions = []
        # Track whether or not ExprRange operands are using
        # "explicit" parameterization, becuase the operators must
        # follow suit.
        using_explicit_parameterization = []
        for sub_expr in self:
            if isinstance(sub_expr, ExprRange):
                # Handle an ExprRange entry; here the "sub-expressions"
                # are really ExprRange "checkpoints" (first, last, as
                # well as the ExprRange body in the middle if using
                # an 'explicit' style for 'parameterization) as well as
                # ellipses between the checkpoints..
                using_explicit_parameterization.append(
                    sub_expr._use_explicit_parameterization(format_type))
                if isinstance(sub_expr.body, ExprTuple):
                    _fence = True
                else:
                    _fence = sub_fence
                formatted_sub_expressions += sub_expr._formatted_checkpoints(
                    format_type, fence=_fence, with_ellipses=True,
                    operator=operator_or_operators)
            elif isinstance(sub_expr, ExprTuple):
                # always fence nested expression lists
                formatted_sub_expressions.append(
                    sub_expr.formatted(format_type, fence=True))
            else:
                formatted_sub_expressions.append(
                    sub_expr.formatted(format_type, fence=sub_fence))

        # put the formatted operator between each of formatted_sub_expressions
        for wrap_position in wrap_positions:
            if wrap_position % 2 == 1:
                # wrap after operand (before next operation)
                formatted_sub_expressions[(wrap_position - 1) // 2] += r' \\ '
            else:
                # wrap after operation (before next operand)
                formatted_sub_expressions[wrap_position // 2] = r' \\ ' + \
                    formatted_sub_expressions[wrap_position // 2]
        if operator_or_operators is None:
            operator_or_operators = ','
        elif isinstance(operator_or_operators, Expression) and not isinstance(operator_or_operators, ExprTuple):
            operator_or_operators = operator_or_operators.formatted(
                format_type)
        if isinstance(operator_or_operators, str):
            # single operator
            formatted_operator = operator_or_operators
            if operator_or_operators == ',':
                # e.g.: a, b, c, d
                out_str += (formatted_operator +
                            ' ').join(formatted_sub_expressions)
            else:
                # e.g.: a + b + c + d
                out_str += (' ' + formatted_operator +
                            ' ').join(formatted_sub_expressions)
        else:
            # assume all different operators
            formatted_operators = []
            for operator in operator_or_operators:
                if isinstance(operator, ExprRange):
                    # Handle an ExprRange entry; here the "operators"
                    # are really ExprRange "checkpoints" (first, last,
                    # as well as the ExprRange body in the middle if
                    # using an 'explicit' style for 'parameterization').
                    # For the 'ellipses', we will just use a
                    # placeholder.
                    be_explicit = using_explicit_parameterization.pop(0)
                    formatted_operators += operator._formatted_checkpoints(
                        format_type, fence=sub_fence, ellipses='',
                        use_explicit_parameterization=be_explicit)
                elif isinstance(operator, str):
                    formatted_operators.append(operator)
                else:
                    formatted_operators.append(operator.formatted(format_type))
            if len(formatted_sub_expressions) == len(formatted_operators):
                # operator preceeds each operand
                if implicit_first_operator:
                    # first operator is implicit
                    out_str = formatted_sub_expressions[0]
                else:
                    # no space after first operator
                    out_str = formatted_operators[0] + \
                        formatted_sub_expressions[0]
                out_str += ' '  # space before next operator
                out_str += ' '.join(formatted_operator + ' ' + formatted_operand for formatted_operator,
                                    formatted_operand in zip(formatted_operators[1:], formatted_sub_expressions[1:]))
            elif len(formatted_sub_expressions) == len(formatted_operators) + 1:
                # operator between each operand
                out_str = ' '.join(
                    formatted_operand +
                    ' ' +
                    formatted_operator for formatted_operand,
                    formatted_operator in zip(
                        formatted_sub_expressions,
                        formatted_operators))
                out_str += ' ' + formatted_sub_expressions[-1]
            elif len(formatted_sub_expressions) != len(formatted_operators):
                raise ValueError("May only perform ExprTuple formatting if the number of operators is equal to the number of operands (precedes each operand) or one less (between each operand); also, operator ranges must be in correpsondence with operand ranges.")

        if do_wrapping and format_type == 'latex':
            out_str += r' \end{array}'
        if fence:
            out_str += ')' if format_type == 'string' else r'\right)'

        return out_str

    def num_elements(self, assumptions=USE_DEFAULTS):
        '''
        Return the proven number of elements of this ExprTuple as an 
        Expression.  This includes the extent of all contained ranges.
        '''
        from proveit.core_expr_types import Len
        return Len(self).computed(assumptions)

    def has_matching_ranges(self, other_tuple):
        '''
        Return True iff the `other_tuple` matches this ExprTuple
        with respect to which entries are ExprRanges and, where they
        are, the start and end indices of the ExprRanges match.
        '''
        from proveit import ExprRange, composite_expression
        if not isinstance(other_tuple, ExprTuple):
            other_tuple = composite_expression(other_tuple)
        if len(self.entries) != len(other_tuple):
            return False  # don't have the same number of entries
        for entry, other_entry in zip(self, other_tuple):
            if (isinstance(entry, ExprRange)
                    != isinstance(other_entry, ExprRange)):
                return False  # range vs singular mismatch
            if isinstance(entry, ExprRange):
                if entry.start_index != other_entry.start_index:
                    return False  # start indices don't match
                if entry.end_index != other_entry.end_index:
                    return False  # end indices don't match
        return True  # everything matches.

    def _replaced(self, repl_map, allow_relabeling, reduction_map,
                  assumptions, requirements, equality_repl_requirements):
        '''
        Returns this expression with sub-expressions replaced
        according to the replacement map (repl_map) dictionary.

        'assumptions' and 'requirements' are used when an operator is
        replaced by a Lambda map that has a range of parameters
        (e.g., x_1, ..., x_n) such that the length of the parameters
        and operands must be proven to be equal.  For more details,
        see Operation._replaced, Lambda.apply, and ExprRange._replaced
        (which is the sequence of calls involved).

        For an ExprTuple, each entry is 'replaced' independently.
        For an entry that is an ExprRange, its "replaced entries" are
        embedded as one or more entries of the ExprTuple.
        '''
        from .expr_range import ExprRange
        if len(repl_map) > 0 and (self in repl_map):
            # The full expression is to be replaced.
            return repl_map[self]

        subbed_exprs = []
        for expr in self.entries:
            if isinstance(expr, ExprRange):
                # ExprRange.replaced is a generator that yields items
                # to be embedded into the tuple.
                subbed_exprs.extend(expr._replaced_entries(
                    repl_map, allow_relabeling, reduction_map, assumptions,
                    requirements, equality_repl_requirements))
            else:
                subbed_expr = expr.replaced(
                        repl_map, allow_relabeling, reduction_map,
                        assumptions, requirements, equality_repl_requirements)
                subbed_exprs.append(subbed_expr)

        return self.__class__._checked_make(
            self._core_info, subbed_exprs)

    def merger(self, assumptions=USE_DEFAULTS):
        '''
        If this is an tuple of expressions that can be directly merged
        together into a single ExprRange, return this proven
        equivalence.  For example,
        {j \in Natural, k-(j+1) \in Natural}
        |- (x_1, .., x_j, x_{j+1}, x_{j+2}, ..., x_k) = (x_1, ..., x_k)
        '''
        from proveit._core_.expression.lambda_expr import Lambda
        from .expr_range import ExprRange
        from proveit.relation import TransRelUpdater
        from proveit.core_expr_types.tuples import (
            merge, merge_front, merge_back, merge_extension,
            merge_pair, merge_series)
        from proveit import f, i, j, k, l, x
        from proveit.numbers import Add, one

        # A convenience to allow successive update to the equation via
        # transitivities (starting with self=self).
        eq = TransRelUpdater(self, assumptions)

        # Determine the position of the first ExprRange item and get the
        # lambda map.
        first_range_pos = len(self.entries)
        lambda_map = None
        for _k, item in enumerate(self):
            if isinstance(item, ExprRange):
                lambda_map = Lambda(item.lambda_map.parameter,
                                    item.lambda_map.body)
                first_range_pos = _k
                break

        if 1 < first_range_pos:
            if lambda_map is None:
                raise NotImplementedError("Means of extracting a lambda "
                                          "map has not been implemented")
                pass  # need the lambda map
            # Collapse singular items at the beginning.
            front_singles = ExprTuple(eq.expr[:first_range_pos])
            i_sub = lambda_map.extract_argument(front_singles[0])
            j_sub = lambda_map.extract_argument(front_singles[-1])
            if len(front_singles.entries) == 2:
                # Merge a pair of singular items.
                front_merger = merge_pair.instantiate(
                    {f: lambda_map, i: i_sub, j: j_sub},
                    assumptions=assumptions)
            else:
                # Merge a series of singular items in one shot.
                front_merger = merge_series.instantiate(
                    {f: lambda_map, x: front_singles, i: i_sub, j: j_sub},
                    assumptions=assumptions)
            eq.update(
                front_merger.substitution(
                    self.inner_expr()[
                        :first_range_pos],
                    assumptions=assumptions))

        if eq.expr.num_entries() == 1:
            # We have accomplished a merger down to one item.
            return eq.relation

        if eq.expr.num_entries() == 2:
            # Merge a pair.
            if isinstance(eq.expr[0], ExprRange):
                if isinstance(eq.expr[1], ExprRange):
                    # Merge a pair of ExprRanges.
                    item = eq.expr[1]
                    other_lambda_map = Lambda(item.lambda_map.parameter,
                                              item.lambda_map.body)
                    if other_lambda_map != lambda_map:
                        raise ExprTupleError(
                            "Cannot merge together ExprRanges "
                            "with different lambda maps: %s vs %s" %
                            (lambda_map, other_lambda_map))
                    _i, _j = eq.expr[0].start_index, eq.expr[0].end_index
                    _k, _l = eq.expr[1].start_index, eq.expr[1].end_index
                    merger = \
                        merge.instantiate({f: lambda_map, i: _i, j: _j, k: _k, l: _l},
                                          assumptions=assumptions)
                else:
                    # Merge an ExprRange and a singular item.
                    _i, _j = eq.expr[0].start_index, eq.expr[0].end_index
                    _k = lambda_map.extract_argument(eq.expr[1])
                    if _k == Add(_j, one):
                        merger = merge_extension.instantiate(
                            {f: lambda_map, i: _i, j: _j},
                            assumptions=assumptions)
                    else:
                        merger = merge_back.instantiate(
                            {f: lambda_map, i: _i, j: _j, k: _k},
                            assumptions=assumptions)
            else:
                # Merge a singular item and ExprRange.
                i_sub = lambda_map.extract_argument(eq.expr[0])
                j_sub, k_sub = eq.expr[1].start_index, eq.expr[1].end_index
                merger = \
                    merge_front.instantiate({f: lambda_map, i: i_sub, j: j_sub,
                                             k: k_sub}, assumptions=assumptions)
            eq.update(merger)
            return eq.relation

        while eq.expr.num_entries() > 1:
            front_merger = ExprTuple(*eq.expr[:2].entries).merger(assumptions)
            eq.update(front_merger.substitution(
                eq.expr.inner_expr(assumptions)[:2],
                assumptions=assumptions))
        return eq.relation

    def deduce_equality(self, equality, assumptions=USE_DEFAULTS,
                        minimal_automation=False):
        from proveit import ExprRange
        from proveit.logic import Equals
        if not isinstance(equality, Equals):
            raise ValueError("The 'equality' should be an Equals expression")
        if equality.lhs != self:
            raise ValueError("The left side of 'equality' should be 'self'")

        from proveit.numbers import num, one

        # Handle the special counting cases.  For example,
        #   (1, 2, 3, 4) = (1, ..., 4)
        _n = len(self.entries)
        if all(self[_k] == num(_k + 1) for _k in range(_n)):
            if (isinstance(equality.rhs, ExprTuple)
                    and equality.rhs.num_entries() == 1
                    and isinstance(equality.rhs[0], ExprRange)):
                expr_range = equality.rhs[0]
                if (expr_range.start_index == one and
                        expr_range.end_index == num(_n)):
                    if len(self.entries) >= 10:
                        raise NotImplementedError("counting range equality "
                                                  "not implemented for more "
                                                  "then 10 elements")
                    import proveit.numbers.numerals.decimals
                    equiv_thm = proveit.numbers.numerals.decimals\
                        .__getattr__('count_to_%d_range' % _n)
                    return equiv_thm
        raise NotImplementedError("ExprTuple.deduce_equality not implemented "
                                  "for this case: %s." % self)

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


def is_single(expr_tuple):
    '''
    Return True if this has a single element that is not an
    ExprRange.
    '''
    from .expr_range import ExprRange
    return (len(expr_tuple.entries) == 1 and 
                not isinstance(expr_tuple[0], ExprRange))

def is_double(expr_tuple):
    '''
    Returns True if this has two elements that are not ExprRanges.
    '''
    return len(expr_tuple.entries) == 2 and not expr_tuple.contains_range()

def extract_var_tuple_indices(indexed_var_tuple):
    '''
    Given an ExprTuple of only IndexedVar and ExprRange entries, returns
    an ExprTuple of just the corresponding indices (including ranges of
    indices and nested ranges of indices).
    '''
    from proveit import IndexedVar, ExprRange
    indices = []
    if not isinstance(indexed_var_tuple, ExprTuple):
        raise TypeError("'indexed_var_tuple' must be an ExprTuple")
    for entry in indexed_var_tuple:
        if isinstance(entry, IndexedVar):
            entry_indices = entry.indices
            if is_single(entry_indices):
                indices.append(entry_indices[0])
            else:
                indices.append(entry_indices)
        elif isinstance(entry, ExprRange):
            inner_indices = extract_var_tuple_indices(ExprTuple(entry.body))
            assert inner_indices.num_entries() == 1
            body = inner_indices[0]
            indices.append(ExprRange(entry.parameter, body,
                                     entry.start_index, entry.end_index))
        else:
            raise TypeError("'var_range' must be an ExprTuple only of "
                            "IndexedVar or (nested) ExprRange entries.")
    return ExprTuple(*indices)


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
                "when performing ExprTuple.convert_to_map: %s" % self.extr_msg)
