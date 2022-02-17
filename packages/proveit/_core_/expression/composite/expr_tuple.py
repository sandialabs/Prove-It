from .composite import Composite
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.defaults import defaults, USE_DEFAULTS
from proveit._core_.expression.style_options import StyleOptions
from proveit.decorators import prover, equality_prover


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

    def __init__(self, *expressions, styles=None):
        '''
        Initialize an ExprTuple from an iterable over Expression
        objects.
        '''
        from proveit._core_ import Judgment
        from .composite import single_or_composite_expression
        entries = []
        if isinstance(expressions, str):
            # We should check for strings in particular because this
            # will otherwise lead to an infinite recursion.
            raise TypeError("ExprTuple accepts Expressions, not a str: %s"
            %expressions)
        for entry in expressions:
            if isinstance(entry, Judgment):
                # Extract the Expression from the Judgment:
                entry = entry.expr
            if not isinstance(entry, Expression):
                entry = single_or_composite_expression(entry)
            assert isinstance(entry, Expression)
            entries.append(entry)
        self.entries = tuple(entries)
        
        Expression.__init__(self, ['ExprTuple'], self.entries,
                            styles=styles)

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
    def _make(sub_class, core_info, sub_expressions, *, styles):
        if sub_class != ExprTuple:
            MakeNotImplemented(sub_class)
        if len(core_info) != 1 or core_info[0] != 'ExprTuple':
            raise ValueError("Expecting ExprTuple core_info to contain "
                             "exactly one item: 'ExprTuple'")
        return ExprTuple(*sub_expressions, styles=styles)

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
            'wrap_positions', '').strip('()').split(' ') if pos_str != '']

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(
            self,
            format_type, *,
            fence=True,
            sub_fence=False,
            operator_or_operators=',',
            implicit_first_operator=True,
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

        if isinstance(operator_or_operators, list):
            operators = operator_or_operators
        elif isinstance(operator_or_operators, ExprTuple):
            operators = list(operator_or_operators.entries)
        else:
            operators = [operator_or_operators]*self.num_entries()
        if self.num_entries() == len(operators) + 1:
            # operators between operands -- put a blank 'operator' at
            # the beginning.
            operators = [''] + operators
        if len(operators) != self.num_entries():
            raise ValueError("There should be the same number of operators "
                             "as operands, or 1 less for them to appear "
                             "just between operands: "
                             "%s with %d vs %s with %d"%(
                                     operators, len(operators), 
                                     self.entries, self.num_entries()))
        formatted_entries = [] # in (operator, element/ellipsis) pairs
        implicit_operator = implicit_first_operator
        for sub_expr, operator in zip(self, operators):
            if isinstance(sub_expr, ExprRange):
                formatted_entries += sub_expr._formatted_entries(
                    format_type, 
                    implicit_first_operator=implicit_operator,
                    operator_or_operators=operator)
            else:
                if implicit_operator:
                    operator = ''
                elif isinstance(operator, Expression):
                    operator = operator.formatted(format_type)
                if len(formatted_entries) > 0:
                    if operator not in (',', ';'):
                        operator = ' ' + operator
                    operator = operator + ' '
                if isinstance(sub_expr, ExprTuple):
                    # always fence nested expression lists
                    formatted_entries.append(
                        [operator, sub_expr.formatted(format_type, 
                                                      fence=True)])
                else:
                    formatted_entries.append(
                        [operator, sub_expr.formatted(format_type, 
                                                      fence=sub_fence)])
            implicit_operator = False

        # put the formatted operator between each of formatted_sub_expressions
        for wrap_position in wrap_positions:
            if wrap_position % 2 == 1:
                # wrap after operand (before next operation)
                formatted_entries[(wrap_position - 1) // 2][1] += r' \\ '
            else:
                # wrap after operation (before next operand)
                formatted_entries[wrap_position // 2][0] += r' \\ '
        # The operators are
        out_str += ''.join(''.join([operator, operand]) for
                            operator, operand in formatted_entries)

        if do_wrapping and format_type == 'latex':
            out_str += r' \end{array}'
        if fence:
            out_str += ')' if format_type == 'string' else r'\right)'

        return out_str

    def num_elements(self, proven=True, **defaults_config):
        '''
        Return the number of elements of this ExprTuple as an 
        Expression.  This includes the extent of all contained ranges.
        If proven==True, a proof is constructed in the process.
        '''
        from .expr_range import ExprRange
        from proveit.core_expr_types import Len
        from proveit.numbers import Add, zero, one
        if proven:
            return Len(self).computed(**defaults_config)
        # Do the quick-and-dirty calculation with no proof.
        count = zero
        for entry in self:
            if isinstance(entry, ExprRange):
                count = Add(count, 
                            entry.num_elements(proven=False)).quick_simplified()
            else:
                count = Add(count, one).quick_simplified()
        return count

    def yield_format_cell_info(self):
        '''
        Yield information pertaining to each format cell of this
        ExprTuple in the format:
            ((expr, role), assumptions)
        The expr is the Expression of the entry.  Temporary assumptions
        may be made about the comparison of ExprRange indices at 
        distinct format cells (useful from case simplification of nested
        ExprRanges) and yielded.  The 'role' is defined as follows.
        The beginning cells of the ExprRange will have consecutive 
        integers for their role  starting with 0, the last cell has -1 
        for its role, and the 'ellipsis' cell has 'implicit', 
        'explicit', or 'param_independent' for its role depending upon
        whether it is parameter independent and, if not, the 
        'parameterization' style option of the ExprRange.
        '''
        from .expr_range import ExprRange
        
        for item in self.entries:
            # Append to cell entries.
            if isinstance(item, ExprRange):
                # An ExprRange covers multiple format cells.
                for info in item.yield_format_cell_info():
                    yield info
            else:
                # One format cells for a regular entry.
                yield (item, 'normal'), defaults.assumptions
    
    def get_format_cell_element_positions(self):
        '''
        Returns a list of element positions in correspondence with
        each format cell of this ExprTuple 
        (see ExprTuple.yield_format_cell_info).
        The element position starts as a 'one' (from proveit.numbers) 
        and adds one in correspondence with each format cell except the 
        'ellipsis' cell and the last cell of each ExprRange.  The 
        element position of the 'ellipsis' cells is 'None' (it isn't 
        defined).  The element position of the last cell of the 
        ExprRange will be ('end_index' - 'start_index') of the ExprRange
        added to the element position of the first cell.

        The assumptions dictate simplifications that may apply to
        the element positions.
        '''
        from .expr_range import ExprRange
        from proveit.numbers import Add, zero, one

        element_positions = []
        element_pos = zero # We will add 1 before using this.
        for item in self.entries:
            # Add one to the element_pos.
            element_pos = Add(element_pos, one).quick_simplified()
            # Append to element_positions.
            if isinstance(item, ExprRange):
                # An ExprRange covers multiple format cells.
                element_pos = item._append_format_cell_element_positions(
                        element_pos, element_positions)
            else:
                # One format cells for a regular entry.
                element_positions.append(element_pos)
        return element_positions
    
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
                if entry.true_start_index != other_entry.true_start_index:
                    return False  # start indices don't match
                if entry.true_end_index != other_entry.true_end_index:
                    return False  # end indices don't match
        return True  # everything matches.

    def basic_replaced(self, repl_map, *,
                       allow_relabeling=False, requirements=None):
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

        subbed_entries = []
        for entry in self.entries:
            if isinstance(entry, ExprRange):
                # ExprRange.replaced is a generator that yields items
                # to be embedded into the tuple.
                subbed_entries.extend(entry._replaced_entries(
                    repl_map, allow_relabeling, requirements))
            else:
                subbed_entry = entry.basic_replaced(
                        repl_map, allow_relabeling=allow_relabeling, 
                        requirements=requirements)
                subbed_entries.append(subbed_entry)

        if (len(subbed_entries) == len(self.entries) and 
                all(subbed_entry._style_id == entry._style_id for
                    subbed_entry, entry in 
                    zip(subbed_entries, self.entries))):
            # Nothing change, so don't remake anything.
            return self

        return self.__class__._checked_make(
            self._core_info, subbed_entries, 
            style_preferences=self._style_data.styles)
    
    def find_sub_tuple(self, sub_tuple, start=0, end=None):
        '''
        Return the lowest index (within start and end if provided)
        in this ExprTuple where the given sub_tuple is found. 
        Return -1 if it is not found.  This is analogous to
        string.find.
        '''
        if end is None: end = self.num_entries()  
        if isinstance(sub_tuple, ExprTuple):
            sub_tuple = sub_tuple.entries
        _N = len(sub_tuple)
        entries = self.entries
        
        # Iterate from start to end until we match the pattern.
        for i in range(start, end):
            if entries[i] == sub_tuple[0] and entries[i:i+_N] == sub_tuple:
                return i
        return -1
    
    def is_irreducible_value(self):
        '''
        An ExprTuple is irreducible if and only if all of its entries
        are irreducible.
        '''
        from proveit.logic import is_irreducible_value
        return all(is_irreducible_value(entry) for entry in self.entries)

    @equality_prover('evaluated', 'evaluate')
    def evaluation(self, **defaults_config):
        '''
        Proves that this ExprTuple is equal to an ExprTuple
        with all of its entries evaluated (and ExprRanges reduced).
        '''
        return self.simplification(must_evaluate=True)

    @equality_prover('simplified', 'simplify')
    def simplification(self, *, must_evaluate=False, **defaults_config):
        '''
        Proves that this ExprTuple is equal to an ExprTuple
        with all of its entries simplified (and ExprRanges reduced).
        '''
        from proveit.relation import TransRelUpdater
        from proveit import ExprRange
        expr = self
        eq = TransRelUpdater(expr)
        _k = 0
        for entry in self.entries:
            if isinstance(entry, ExprRange):
                entry_simp = entry.reduction(preserve_all=True)
                num_entries = entry_simp.rhs.num_entries()
            else:
                if must_evaluate:
                    entry_simp = entry.evaluation()
                else:
                    entry_simp = entry.simplification()
                num_entries = 1
            if entry_simp.lhs != entry_simp.rhs:
                expr = eq.update(expr.substitution(entry_simp, 
                                                   start_idx=_k))
            _k += num_entries
        return eq.relation

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Proves that this ExprTuple is equal to an ExprTuple
        with ExprRanges reduced unless these are "preserved"
        expressions.
        '''
        from proveit.relation import TransRelUpdater
        from proveit import ExprRange
        from proveit.logic import is_irreducible_value, EvaluationError
        expr = self
        eq = TransRelUpdater(expr)
        if defaults.preserve_all:
            # Preserve all sub-expressions -- don't simplify.
            return eq.relation
        _k = 0
        for entry in self.entries:
            if isinstance(entry, ExprRange):
                if entry in defaults.preserved_exprs:
                    if must_evaluate:
                        # An ExprRange is not irreducible.
                        raise EvaluationError(self)
                    # Preserve this entry -- don't simplify it.
                    _k += ExprTuple(entry).num_entries()
                    continue
                entry_simp = entry.reduction()
                if must_evaluate and not is_irreducible_value(entry_simp.rhs):
                    raise EvaluationError(self)
                if entry_simp.lhs != entry_simp.rhs:
                    substitution = expr.substitution(
                            entry_simp, start_idx=_k, preserve_all=True)
                    expr = eq.update(substitution)
                _k += entry_simp.rhs.num_entries()
            else:
                if must_evaluate and not is_irreducible_value(entry):
                    raise EvaluationError(self)
                _k += 1
        return eq.relation

    @equality_prover('sub_expr_substituted', 'sub_expr_substitute')
    def sub_expr_substitution(self, new_sub_exprs, **defaults_config):
        '''
        Given new sub-expressions to replace existing sub-expressions,
        return the equality between this Expression and the new
        one with the new sub-expressions.
        '''
        from proveit.core_expr_types.tuples import tuple_eq_via_elem_eq
        from proveit import a, b, i
        _i = self.num_elements()
        _a = self.entries
        _b = new_sub_exprs
        return tuple_eq_via_elem_eq.instantiate(
                {i: _i, a: _a, b: _b})

    @equality_prover('substituted', 'substitute')
    def substitution(self, replacement_eq, start_idx=0,
                     **defaults_config):
        '''
        Prove this ExprTuple equal to an ExprTuple with an element or
        portion substituted.  Substitute the portion with the entry 
        index starting with start_idx.  replacement_eq should be an 
        Equals expression with the element or portion being substituted
        on the left side, and the replacement element or portion on the 
        right side.
        
        For example,
        replacement_eq : |- (b_1, ..., b_0) = ()
        ExprTuple(a, b_1, ..., b_0, c).substitution(replacement_eq, 1)
        returns
        |- (a, b_1, ..., b_0, c) = (a, c)
        '''
        from proveit.core_expr_types.tuples import (
                tuple_elem_substitution, tuple_portion_substitution)
        from proveit import Judgment, a, b, c, d, i, j, k
        from proveit.logic import Equals
        if isinstance(replacement_eq, Judgment):
            replacement_eq = replacement_eq.expr
        if not isinstance(replacement_eq, Equals):
            raise TypeError("'replacement_eq' should be an Equals (or "
                            "Judgment for an Equals).")
        if isinstance(replacement_eq.lhs, ExprTuple):
            if not isinstance(replacement_eq.rhs, ExprTuple):
                raise TypeError("'replacement_eq.rhs' should be an ExprTuple"
                                "if 'replacement_eq.lhs' is an ExprTuple.")
            if (start_idx==0 and 
                replacement_eq.lhs.num_entries()==self.num_entries()):
                # Replacing the entire ExprTuple:
                return replacement_eq.prove()

            _a = self[:start_idx]
            end_idx = start_idx + replacement_eq.lhs.num_entries()
            _b = self[start_idx:end_idx]
            _c = self[end_idx:]
            _d = replacement_eq.rhs
            if _b != replacement_eq.lhs:
                raise ValueError(
                        "The 'lhs' of %s expected to match the portion of %s "
                        "starting at %d"%(replacement_eq, self, start_idx))
            _i, _j, _k = _a.num_elements(), _b.num_elements(), _c.num_elements()
            return tuple_portion_substitution.instantiate(
                        {a:_a, b:_b, c:_c, d:_d, i:_i, j:_j, k:_k},
                        preserve_all=True)
        else:
            _a = self[:start_idx]
            _b = self[start_idx]
            _c = self[start_idx+1:]
            _d = replacement_eq.rhs
            if _b != replacement_eq.lhs:
                raise ValueError(
                        "The 'lhs' of %s expected to match the portion of %s "
                        "starting at %d"%(replacement_eq, self, start_idx))
            _i, _k = _a.num_elements(), _c.num_elements()
            return tuple_elem_substitution.instantiate(
                    {a:_a, b:_b, c:_c, d:_d, i:_i, k:_k},
                    preserve_all=True)
            

    @equality_prover('merged', 'merge')
    def merger(self, **defaults_config):
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
        eq = TransRelUpdater(self)

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
                    {f: lambda_map, i: i_sub, j: j_sub})
            else:
                # Merge a series of singular items in one shot.
                front_merger = merge_series.instantiate(
                    {f: lambda_map, x: front_singles, i: i_sub, j: j_sub})
            eq.update(
                front_merger.substitution(
                    self.inner_expr()[:first_range_pos]))

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
                    _i, _j = eq.expr[0].true_start_index, eq.expr[0].true_end_index
                    _k, _l = eq.expr[1].true_start_index, eq.expr[1].true_end_index
                    merger = \
                        merge.instantiate(
                                {f: lambda_map, i: _i, j: _j, k: _k, l: _l})
                else:
                    # Merge an ExprRange and a singular item.
                    _i, _j = eq.expr[0].true_start_index, eq.expr[0].true_end_index
                    _k = lambda_map.extract_argument(eq.expr[1])
                    if _k == Add(_j, one):
                        merger = merge_extension.instantiate(
                            {f: lambda_map, i: _i, j: _j})
                    else:
                        merger = merge_back.instantiate(
                            {f: lambda_map, i: _i, j: _j, k: _k})
            else:
                # Merge a singular item and ExprRange.
                i_sub = lambda_map.extract_argument(eq.expr[0])
                j_sub, k_sub = eq.expr[1].true_start_index, eq.expr[1].true_end_index
                merger = \
                    merge_front.instantiate({f: lambda_map, i: i_sub, 
                                             j: j_sub, k: k_sub})
            eq.update(merger)
            return eq.relation

        while eq.expr.num_entries() > 1:
            front_merger = ExprTuple(*eq.expr[:2].entries).merger()
            eq.update(front_merger.substitution(
                eq.expr.inner_expr()[:2]))
        return eq.relation

    @equality_prover('equated', 'equate')
    def deduce_equality(self, equality, **defaults_config):
        from proveit import ExprRange
        from proveit import a, b, i
        from proveit.logic import Equals
        from proveit.core_expr_types.tuples import tuple_eq_via_elem_eq
        from proveit.relation import TransRelUpdater
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
                if (expr_range.true_start_index == one and
                        expr_range.true_end_index == num(_n)):
                    if len(self.entries) >= 10:
                        raise NotImplementedError("counting range equality "
                                                  "not implemented for more "
                                                  "then 10 elements")
                    import proveit.numbers.numerals.decimals
                    equiv_thm = proveit.numbers.numerals.decimals\
                        .__getattr__('count_to_%d_range' % _n)
                    return equiv_thm
        
        lhs, rhs = equality.lhs, equality.rhs
        if (lhs.num_entries() == rhs.num_entries() == 1
                and isinstance(lhs[0], ExprRange) 
                and isinstance(rhs[0], ExprRange)):
            # Prove the equality of two ExprRanges.
            r_range = rhs[0]
            expr = lhs
            if expr[0].is_decreasing():
                # We could handle different styles later, but
                # let's be consistent with increasing order for now
                # to make this easier to implement.
                expr = expr.inner_expr()[0].with_increasing_order()
            eq = TransRelUpdater(expr)
            if expr[0].true_start_index != r_range.true_start_index:
                # Shift indices so they have the same start.
                expr = eq.update(expr[0].shift_equivalence(
                        new_start=r_range.true_start_index))
            if expr[0].lambda_map != r_range.lambda_map:
                # Change the lambda map.
                expr = eq.update(expr[0].range_fn_transformation(
                        r_range.lambda_map))
            if expr[0].true_end_index != r_range.true_end_index:
                # Make the end indices be the same:
                end_eq = Equals(expr[0].true_end_index, r_range.true_end_index).prove()
                expr = eq.update(end_eq.substitution(
                        expr.inner_expr()[0].true_end_index))
            return eq.relation
        
        # Try tuple_eq_via_elem_eq as the last resort.
        _i = lhs.num_elements()
        _a = lhs
        _b = rhs
        return tuple_eq_via_elem_eq.instantiate({i:_i, a:_a, b:_b})
    
    @equality_prover('expanded_range', 'expand_range')
    def range_expansion(self, **defaults_config):
        '''
        For self an ExprTuple with a single entry that is an ExprRange
        of the form f(i),...,f(j), where 0 <= (j-i) <= 9 (i.e. the
        ExprRange represents 1 to 10 elements), derive and
        return an equality between self and an ExprTuple with explicit
        entries replacing the ExprRange. For example, if
            self = ExprTuple(f(3),...,f(6)),
        then self.range_expansion() would return:
        |- ExprTuple(f(3),...,f(6)) = ExprTuple(f(3), f(4), f(5), f(6))
        '''

        # Check that we have a an ExprTuple with
        # (1) a single entry
        # (2) and the single entry is an ExprRange
        # (these restrictions can be relaxed later to make the
        # method more general)

        # ExprTuple with single entry
        if not self.num_entries() == 1:
            raise ValueError(
                    "ExprTuple.range_expansion() implemented only for "
                    "ExprTuples with a single entry (and the single "
                    "entry must be an ExprRange). Instead, the ExprTuple "
                    "{0} has {1} entries.".format(self, self.num_entries))

        # and the single entry is an ExprRange:
        from proveit import ExprRange
        if not isinstance(self.entries[0], ExprRange):
            raise ValueError(
                    "ExprTuple.range_expansion() implemented only for "
                    "ExprTuples with a single entry (and the single "
                    "entry must be an ExprRange). Instead, the ExprTuple "
                    "is {0}.".format(self))

        from proveit import Function
        from proveit.logic import EvaluationError
        from proveit.numbers import subtract

        _the_expr_range = self[0]

        # _n = self.num_elements()
        try:
            _n = subtract(self[0].true_end_index, self[0].true_start_index).evaluated()
        except EvaluationError as the_error:
            _diff = subtract(self[0].true_end_index, self[0].true_start_index)
            print("EvaluationError: {0}. The ExprRange {1} must represent "
                  "a known, finite number of elements, but all we know is "
                  "that it represents {2} elements.".format(
                    the_error, self[0], _diff))
            raise EvaluationError(
                subtract(self[0].true_end_index, self[0].true_start_index))
        
        _n = _n.as_int() + 1 # actual number of elems being represented
        if not (1 <= _n and _n <= 9):
            raise ValueError(
                    "ExprTuple.range_expansion() implemented only for "
                    "ExprTuples with a single entry, with the single "
                    "entry being an ExprRange representing a finite "
                    "number of elements n with 1 <= n <= 9. Instead, "
                    "the ExprTuple is {0} with number of elements equal "
                    "to {1}.".format(self[0], _n))

        # id the correct theorem for the number of entries
        import proveit.numbers.numerals.decimals
        expansion_thm = proveit.numbers.numerals.decimals\
                        .__getattr__('range_%d_expansion' % _n)

        # instantiate and return the identified expansion theorem
        _f, _i, _j = expansion_thm.instance_vars
        _safe_var = self.safe_dummy_var()
        _idx_param = _the_expr_range.parameter
        _fxn_sub = _the_expr_range.body.basic_replaced(
                {_idx_param: _safe_var})
        _i_sub = _the_expr_range.true_start_index
        _j_sub = _the_expr_range.true_end_index
        return expansion_thm.instantiate(
                {Function(_f, _safe_var): _fxn_sub, _i: _i_sub, _j: _j_sub})

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
                                     entry.true_start_index, entry.true_end_index))
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
