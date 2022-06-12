from .composite import Composite
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.defaults import defaults, USE_DEFAULTS
from proveit._core_.expression.style_options import StyleOptions
from proveit.decorators import prover, relation_prover, equality_prover


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

    def _auto_simplified_sub_exprs(
            self, *, requirements, stored_replacements,
            markers_and_marked_expr):
        '''
        Helper method for _auto_simplified to handle auto-simplification
        replacements for sub-expressions.
        '''
        from proveit import ExprRange, safe_dummy_vars
        from proveit._core_.expression.expr import MarkedExprError
        from proveit._core_.expression.lambda_expr.lambda_expr import (
                get_param_var)
        # When we have a marked expression to dictate which
        # sub-expressions to auto-simplify, it requires extra care
        # because ExprRanges may expand.
        if markers_and_marked_expr is None:
            return Expression._auto_simplified_sub_exprs(
                    self, requirements=requirements, 
                    stored_replacements=stored_replacements, 
                    markers_and_marked_expr=None)
        # Recurse into the sub-expressions.
        # Use a trial-and-error strategy for dealing with
        # the alignment ambiguity from expression range expansions.
        subbed_entries = []
        possibly_expanded_range = False
        prev_possibly_expanded_ranges_start = None
        _j = _k = 0
        num_entries = self.num_entries()
        entries = self.entries
        orig_markers, orig_marked_expr = markers_and_marked_expr
        markers = orig_markers
        if not isinstance(orig_marked_expr, ExprTuple):
            if orig_marked_expr in markers:
                # The entire ExprTuple is marked, so this entire
                # sub-expression is fair game for auto-simplification.
                return Expression._auto_simplified_sub_exprs(
                        requirements=requirements, 
                        stored_replacements=stored_replacements, 
                        markers_and_marked_expr=None)                
            raise MarkedExprError(orig_marked_expr, self)
        orig_marked_expr_entries = orig_marked_expr.entries
        num_orig_marked_expr_entries = len(orig_marked_expr_entries)
        while _j < num_entries:
            entry = entries[_j]
            if _k >= num_orig_marked_expr_entries:
                # self goes beyond what marked expression accounts for.
                raise MarkedExprError(orig_marked_expr, self)
            marked_expr = orig_marked_expr.entries[_k]
            if not possibly_expanded_range:
                possibly_expanded_range = False
                if isinstance(marked_expr, ExprRange):
                    for _var_range in marked_expr._parameterized_var_ranges():
                        if get_param_var(_var_range) in markers:
                            # This is an ExprRange that may have been
                            # expanded.
                            possibly_expanded_range = True
            if possibly_expanded_range and (
                    prev_possibly_expanded_ranges_start is None):
                prev_possibly_expanded_ranges_start = _j
            try:
                while True:
                    try:
                        subbed_entry = entry._auto_simplified(
                            requirements=requirements, 
                            stored_replacements=stored_replacements,
                            markers_and_marked_expr=(markers, marked_expr))
                        break
                    except MarkedExprError as e:
                        if possibly_expanded_range and isinstance(
                                marked_expr, ExprRange):
                            # This trial failed, but we need to try
                            # different possibly forms from an ExprRange
                            # expansion.
                            marker = next(iter(markers))
                            if marked_expr.true_start_index not in markers or (
                                    marked_expr.true_end_index not in markers):
                                # First, try replacing the start and end
                                # with markers -- we don't have to match
                                # them precisely if the range was 
                                # expanded.
                                new_marker1, new_marker2 = safe_dummy_vars(
                                        2, marked_expr)
                                marked_expr = ExprRange(
                                        marked_expr.parameter, 
                                        marked_expr.body, 
                                        new_marker1, new_marker2)
                                markers = tuple(orig_markers) + (
                                        new_marker1, new_marker2)
                                continue
                            # Next try using the marked expressions
                            # body with its parameter replaced by a
                            # marker to capture the possibility to
                            # individual elements extracted during the
                            # expansion.
                            marked_expr = marked_expr.body.basic_replaced(
                                    {marked_expr.parameter:marker})
                            continue
                        raise e
            except MarkedExprError as e:
                if possibly_expanded_range:
                    # Assume the expansion ended, so go to the next
                    # marked expression entry.
                    possibly_expanded_range = False
                    # Increase _k without increasing _j.
                    _k += 1
                    continue
                elif prev_possibly_expanded_ranges_start is not None:
                    # It's conceivable that we thought the previous
                    # expansion went further than it actually did.
                    if _j > prev_possibly_expanded_ranges_start:
                        # We can back up until we are taking the
                        # previous expression range to be empty.
                        _j -= 1 # backup
                        subbed_entries.pop(-1)
                        continue
                raise e # It failed.
            if not possibly_expanded_range:
                # Got beyond any previous possibly-expanded range.
                prev_possibly_expanded_ranges_start = None
            # Lock in this next substituted... for now.
            subbed_entries.append(subbed_entry)
            # Only go to the next entry of the marked expression
            # if we know we are beyond a possibly expanded range.
            if not possibly_expanded_range:
                _k += 1
            _j += 1
        if possibly_expanded_range:
            # There cannot be anything more to the range expansion
            # since 'self' has no more entries.
            _k += 1
        if _k < num_orig_marked_expr_entries:
            # self falls short of what the marked expression
            # accounts for.
            raise MarkedExprError(orig_marked_expr, self)            
        
        sub_exprs, subbed_sub_exprs = entries, subbed_entries
        if all(subbed_sub._style_id == sub._style_id for
               subbed_sub, sub in zip(subbed_sub_exprs, sub_exprs)):
            # Nothing change, so don't remake anything.
            return self
        return self.__class__._checked_make(
            self._core_info, subbed_sub_exprs,
            style_preferences=self._style_data.styles)

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
    
    def _build_canonical_form(self):
        '''
        Returns a form of this ExprTuple with operands in their
        canonical forms.  ExprRanges are shifted to start with an
        index of 1.     
        '''
        from proveit.numbers import one, Add, Neg
        from .expr_range import ExprRange
        entries = []
        for entry in self.entries:
            if isinstance(entry, ExprRange):
                parameter = entry.parameter
                orig_start_index = entry.true_start_index
                _n = entry.num_elements(proven=False)
                if orig_start_index == one:
                    shifted_body = entry.body
                else:
                    shifted_body = entry.body.basic_replaced(
                            {parameter:Add(parameter, 
                                           orig_start_index,
                                           Neg(one)).quick_simplified()})
                entry = ExprRange(parameter, shifted_body.canonical_form(), 
                                  one, _n)
            else:
                entry = entry.canonical_form()
            entries.append(entry)
        return ExprTuple(*entries)
    
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

    @relation_prover
    def deduce_equal_or_not(self, other_tuple, **defaults_config):
        '''
        Prove and return that this ExprTuple is either equal or
        not equal to other_tuple or raises an UnsatisfiedPrerequisites
        or NotImplementedError if we cannot readily prove either of
        these.
        '''
        from proveit import (ExprRange, safe_dummy_var,
                             ProofFailure, UnsatisfiedPrerequisites)
        from proveit.logic import (
                And, Or, Equals, NotEquals, deduce_equal_or_not)
        from proveit.numbers import Less
        if self == other_tuple:
            return Equals(self, other_tuple).conclude_via_reflexivity
        if not isinstance(other_tuple, ExprTuple):
            raise TypeError("Expecting 'other_tuple' to be an ExprTuple "
                            "not a %s"%other_tuple.__class__)
        _i = self.num_elements()
        _j = other_tuple.num_elements()
        try:
            deduce_equal_or_not(_i, _j)
        except UnsatisfiedPrerequisites:
             Less.sort([_i, _j]) # try sorting
        if NotEquals(_i, _j).proven():
            # Not equal because the lengths are different.
            return self.not_equal(other_tuple)
        elif not Equals(_i, _j).proven():
            raise UnsatisfiedPrerequisites(
                    "Unable to prove wether or not the lengths of "
                    "%s and %s are equal"%(self, other_tuple))
        
        def raise_non_corresponding():
            raise NotImplementedError(
                    "ExprTuple.deduce_equal_or_not is only "
                    "implemented for the case when ExprRanges "
                    "match up: %s vs %s"%self, other_tuple)
            
        if self.num_entries() == other_tuple.num_entries():
            if self.num_entries()==1 and self.contains_range():
                if not other_tuple.contains_range():
                    # One ExprTuple has a range but the other doesn't.
                    # That case isn't handled.
                    raise_non_corresponding()
                lhs_range = self.entries[0]
                rhs_range = other_tuple.entries[0]
                start_index = lhs_range.start_index
                end_index = lhs_range.end_index
                if (start_index != rhs_range.start_index):
                    shift_equiv = rhs_range.shift_equivalence(
                            new_start = start_index)
                    return self.deduce_equal_or_not(
                            shift_equiv.rhs).apply_transitivity(
                                    shift_equiv)
                if end_index != rhs_range.end_index:
                    try:
                        Equals(end_index, rhs_range.end_index).prove()
                    except (ProofFailure, UnsatisfiedPrerequisites,
                            NotImplementedError):
                        # Indices must match for a proper correspondence.
                        raise_non_corresponding()
                if lhs_range.parameter != rhs_range.parameter:
                    # Use a safe common parameter.
                    param = safe_dummy_var(lhs_range.body, rhs_range.body)
                    lhs_range_body = lhs_range.body.basic_replaced(
                            {lhs_range.parameter: param})
                    rhs_range_body = rhs_range.body.basic_replaced(
                            {rhs_range.parameter: param})
                else:
                    param = lhs_range.parameter
                    lhs_range_body = lhs_range.body
                    rhs_range_body = rhs_range.body
                inner_assumptions = defaults.assumptions + (
                        lhs_range.parameter_condition(),)
                try:
                    body_relation = deduce_equal_or_not(
                            lhs_range_body, rhs_range_body,
                            assumptions=inner_assumptions)
                    if isinstance(body_relation, Equals):
                        # Every element is equal, so the ExprTuples 
                        # are equal.
                        return self.deduce_equality(
                                Equals(self, other_tuple))
                    else:
                        # Every element is not equal, so the ExprTuples 
                        # are not equal.
                        # This will enable "any" from "all".
                        And(ExprRange(
                                param, NotEquals(lhs_range_body,
                                                 rhs_range_body),
                                start_index, end_index)).prove()
                        return self.not_equal(other_tuple)
                except (NotImplementedError, UnsatisfiedPrerequisites):
                    pass
                if And(ExprRange(param, Equals(lhs_range_body, 
                                               rhs_range_body),
                                 start_index, end_index)).proven():
                    # Every element is equal, so the ExprTuples 
                    # are equal.
                    return self.deduce_equality(
                            Equals(self, other_tuple))
                elif Or(ExprRange(param, NotEquals(lhs_range_body,
                                                   rhs_range_body),
                        start_index, end_index)).proven():
                    # Some element pair is not equal, so the ExprTuples 
                    # are not equal.
                    return self.not_equal(other_tuple)
                raise UnsatisfiedPrerequisites(
                        "Could not determine whether %s = %s"
                        %(self, other_tuple))
            
            # Loop through each entry pair in correspondence and
            # see if we can readily prove whether or not they are
            # all equal.
            for idx, (_x, _y) in enumerate(
                    zip(self.entries, other_tuple.entries)):
                if isinstance(_x, ExprRange) != isinstance(_y, ExprRange):
                    raise_non_corresponding()
                if _x == _y:
                    # The expressions are the same, so we know they
                    # are equal.
                    continue
                if isinstance(_x, ExprRange):
                    # Wrap ExprRanges in ExprTuples and compare as
                    # single entry tuples.
                    _x = ExprTuple(_x)
                    _y = ExprTuple(_y)
                    _k = _x.num_elements()
                    _l = _y.num_elements()
                    size_relation = deduce_equal_or_not(_k, _l)
                    if isinstance(size_relation.expr, NotEquals):
                        # Not implemented when the ExprRanges don't
                        # correspond in size.
                        raise_non_corresponding()
                    relation = deduce_equal_or_not(_x, _y)
                else:
                    # Compare singular entries.
                    relation = deduce_equal_or_not(_x, _y)
                if isinstance(relation.expr, NotEquals):
                    # Aha! They are not equal.
                    return self.not_equal(other_tuple)
            # They are equal!
            return self.deduce_equality(Equals(self, other_tuple))

        raise NotImplementedError(
                    "ExprTuple.deduce_equal_or_not is not implemented "
                    "for ExprTuples that have a different number of "
                    "entries.")

    @relation_prover
    def not_equal(self, other_tuple, *,
                  neq_with_diff_len_thm=None,
                  neq_via_any_elem_neq_thm=None,
                  **defaults_config):
        '''
        Prove and return this ExprTuple not equal to the other
        ExprTuple.
        '''
        from proveit import a, b, i, j, UnsatisfiedPrerequisites
        from proveit.logic import NotEquals, deduce_equal_or_not
        from proveit.numbers import Less
        from proveit.core_expr_types.tuples import (
                tuple_neq_with_diff_len, tuple_neq_via_any_elem_neq)
        if not isinstance(other_tuple, ExprTuple):
            raise TypeError("Expecting 'other_tuple' to be an ExprTuple "
                            "not a %s"%other_tuple.__class__)  
        _a = self
        _b = other_tuple
        _i = _a.num_elements()
        _j = _b.num_elements()
        try:
            deduce_equal_or_not(_i, _j)
        except UnsatisfiedPrerequisites:
             Less.sort([_i, _j]) # try sorting
        if NotEquals(_i, _j).proven():
            # Not equal because the lengths are different.
            if neq_with_diff_len_thm is None:
                neq_with_diff_len_thm = tuple_neq_with_diff_len
            return neq_with_diff_len_thm.instantiate(
                    {i:_i, j:_j, a:self, b:other_tuple})
        else:
            # Use the general theorem for proving tuples are not equal
            # if any corresponding elements are not equal.
            if neq_via_any_elem_neq_thm is None:
                neq_via_any_elem_neq_thm = tuple_neq_via_any_elem_neq
            return neq_via_any_elem_neq_thm.instantiate(
                    {i:_i, a:_a, b:_b})

    @equality_prover('merged', 'merge')
    def merger(self, **defaults_config):
        '''
        If this is an tuple of expressions that can be directly merged
        together into a single ExprRange, return this proven
        equivalence.  For example,
        {j \in Natural, k-(j+1) \in Natural}
        |- (x_1, .., x_j, x_{j+1}, x_{j+2}, ..., x_k) = (x_1, ..., x_k)
        '''
        from proveit._core_.expression.lambda_expr import (
                Lambda, ArgumentExtractionError)
        from .expr_range import ExprRange, simplified_index
        from proveit.relation import TransRelUpdater
        from proveit.core_expr_types.tuples import (
            merge, merge_front, merge_back, merge_extension,
            merge_pair, merge_series)
        from proveit import f, i, j, k, l, x
        from proveit.numbers import one, Add, subtract

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
                    try:
                        _k = lambda_map.extract_argument(eq.expr[1])
                    except ArgumentExtractionError:
                        _k = simplified_index(Add(_j, one))
                    if _k == Add(_j, one):
                        merger = merge_extension.instantiate(
                            {f: lambda_map, i: _i, j: _j})
                    else:
                        merger = merge_back.instantiate(
                            {f: lambda_map, i: _i, j: _j, k: _k})
            else:
                # Merge a singular item and ExprRange.
                _i = simplified_index(
                    subtract(eq.expr[1].true_start_index, one))
                _j, _k = eq.expr[1].true_start_index, eq.expr[1].true_end_index
                merger = \
                    merge_front.instantiate({f: lambda_map, i: _i, 
                                             j: _j, k: _k})
            all_decreasing = all(expr.is_decreasing() for expr in eq.expr
                                 if isinstance(expr, ExprRange))
            if all_decreasing:
                # Apply the 'decreasing' order style to match what we
                # had originally.
                for _i in (0, 1):
                    if isinstance(eq.expr[_i], ExprRange):
                        merger = (merger.inner_expr().lhs[_i]
                                  .with_decreasing_order())
                merger = merger.inner_expr().rhs[0].with_decreasing_order()
            eq.update(merger)
            return eq.relation

        while eq.expr.num_entries() > 1:
            front_merger = ExprTuple(*eq.expr[:2].entries).merger()
            eq.update(front_merger.substitution(
                eq.expr.inner_expr()[:2]))
        return eq.relation

    @equality_prover('equated', 'equate')
    def deduce_equality(self, equality, *,
                        eq_via_elem_eq_thm=None, **defaults_config):
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
        _a_orig = lhs
        _b_orig = rhs
        
        _a, _b = ExprTuple.align_ranges(_a_orig, _b_orig)        
        if eq_via_elem_eq_thm is None:
            eq_via_elem_eq_thm = tuple_eq_via_elem_eq
        equality = eq_via_elem_eq_thm.instantiate({i:_i, a:_a, b:_b})
        # Substitute back in the originals if changed for alignment
        # purposes.
        if _a != _a_orig:
            equality = equality.inner_expr().lhs.substitute(_a_orig)
        if _b != _b_orig:
            equality = equality.inner_expr().rhs.substitute(_b_orig)
        return equality

    @staticmethod
    def align_ranges(*expr_tuples, equations=None, 
                     reversed_equations=None):
        '''
        Given a collection of ExprTuples that all represent the same 
        number of elements, align any expression ranges so they all
        of the same start and end indices.  Partition and/or shift 
        ranges as necessary to make sure they all line up.
        
        Returns a collection of ExprTuples that equate to the originals,
        respectively, but are aligned to each other.
        If equations is provided as a list, the equations from
        each original to its 'aligned' (returned) version is appended.
        If reversed_equations is provided as a list, the equations from
        each 'aligned' (returned) version to its original is appended.
        
        For example (as might be appended to 'equations'):
            (a, b_1, ..., b_n, c) = (a, b_1, ..., b_{n-1}, b_n, c)
            (x_1, ..., x_n, y, z) = (x_1, x_{1+1}, ..., x_{n-1+1}, y, z)
        
        As a convention, we will use the start indices from ExprRanges
        within the first of the given ExprTuples to set all of the start
        indices.
        
        Such transformations may be useful before calling instantiate
        on something which has ExprRanges involving multiple indexed 
        parameters.
        For example:
            forall_{n in N+} forall_{x1, ..., x_{n+1}
               [(x_1 = x_{1+1}) and ... and x_n = x_{n+1}] =>
               x_1 = x_{n+1}
            Here, the alternative equivalent expansions should be 
            provided for (x_1, ..., x_n, x_{n+1}) 
            and (x_1, x_{1+1}, ... x_{n+1}) such that the x_1, ... x_n
            portion of the former lines up with the 
            x_{1+1}, ..., x_{n+1} portion of the latter.
        '''
        from proveit import (ExprRange, ProofFailure, 
                             UnsatisfiedPrerequisites)
        from proveit.relation import TransRelUpdater
        from proveit.logic import Equals
        from proveit.numbers import zero, one, Less, LessEq, Add, Neg
        if len(expr_tuples) == 0:
            return tuple() # nothing given, nothing returned.

        if equations is not None:
            if not isinstance(equations, list):
                raise TypeError("Expecting 'equations' to be a list so "
                                "we can append to it")
        if reversed_equations is not None:
            if not isinstance(reversed_equations, list):
                raise TypeError("Expecting 'reversed_equations' to be "
                                "a list so we can append to it.")
        
        def raiseFailureToAlign(msg):
            raise UnsatisfiedPrerequisites(
                    "Unable to align these ExprTuples: %s.  %s."%
                    (expr_tuples, msg))

        remaining_entries_reversed = []
        trans_rel_updaters = []
        for expr_tuple in expr_tuples:
            remaining_entries_reversed.append(list(reversed(
                    expr_tuple.entries)))
            trans_rel_updaters.append(TransRelUpdater(expr_tuple))
        idx = 0
        while True > 0:
            # Find the minimum number of elements contained in any
            # of the first entries of what remains (the last in the
            # reversed direction).  Where there are empty-range entries
            # reduce them and move on.
            min_entry_length = None
            for _k, (reversed_entries, updater) in enumerate(
                    zip(remaining_entries_reversed, trans_rel_updaters)):
                print(_k, updater.expr)
                while True:
                    if len(reversed_entries) == 0:
                        entry = None
                        break
                    entry = reversed_entries[-1]
                    if isinstance(entry, ExprRange):
                        num_elements = entry.num_elements(proven=False)
                        # First see if there are 0 elements in this entry
                        try:
                            relation_with_zero = Less.sort(
                                    [zero, num_elements])
                        except (ProofFailure, UnsatisfiedPrerequisites):
                            # It may be ambiguous; that's ok.
                            pass
                        if isinstance(relation_with_zero.expr, Equals):
                            # There are 0 elements in this entry.
                            # reduce it.
                            updater.update(updater.inner_expr()[idx].
                                           reduction())
                            reversed_entries.pop(-1)
                            continue # grab the next entry
                    break
                if entry is None:
                    # Indicate that we got the end on one of them.
                    # If we got to the end on one, we must make it to
                    # the end on all of them.
                    if min_entry_length is None:
                        min_entry_length = 0
                    else:
                        # Got to the end this one but not previously.
                        raiseFailureToAlign("Lengths don't appear to be "
                                            "equal")
                    break
                if min_entry_length == 0:
                    # Got to the end on a previous one but not this one.
                    raiseFailureToAlign("Lengths don't appear to be "
                                        "equal")
                print(_k, updater.expr)
                if isinstance(entry, ExprRange):
                    if min_entry_length not in (None, one):
                        # See if this is below the previous minimum.
                        try:
                            relation_with_min = Less.sort(
                                    [min_entry_length, num_elements]).expr
                        except (ProofFailure, UnsatisfiedPrerequisites):
                            raiseFailureToAlign(
                                    "Unable to determine sorted order "
                                    "%s and %s"
                                    %(num_elements, min_entry_length))
                        if not isinstance(relation_with_min, Equals) and (
                                relation_with_min.normal_lhs == num_elements):
                            # num_elements < min_entry_length:
                            min_entry_length = num_elements
                    elif min_entry_length is None:
                        min_entry_length = num_elements
                else:
                    min_entry_length = one
            if min_entry_length == 0:
                # Got to the end of all of the ExprTuples.
                break
            assert min_entry_length is not None

            # We've eliminated zero-length ranges and determined the
            # minimum entry length.  Now let's establish the next entry.
            start_index = end_index = None
            for _k, (reversed_entries, updater) in enumerate(
                    zip(remaining_entries_reversed, trans_rel_updaters)):
                print(_k, updater.expr)
                entry = reversed_entries.pop(-1)
                if isinstance(entry, ExprRange):
                    try:
                        relation_with_min = LessEq.sort(
                                [min_entry_length, 
                                 entry.num_elements(proven=False)],
                                 reorder=False).expr
                    except (ProofFailure, UnsatisfiedPrerequisites):
                        raiseFailureToAlign(
                                "Unable to determine sorted order "
                                "%s and %s"
                                %(num_elements, min_entry_length))
                    if not isinstance(relation_with_min, Equals):
                        # We must partition this ExprRange.
                        if min_entry_length == one:
                            partition_idx = entry.true_start_index
                        else:
                            partition_idx = Add(
                                    entry.true_start_index, min_entry_length,
                                    Neg(one)).simplified_index()
                        updater.update(
                                updater.inner_expr()[idx].partition(
                                        partition_idx, 
                                        force_to_treat_as_increasing=True))
                        # Append the remainder of the ExprRange.
                        reversed_entries.append(updater.expr.entries[idx+1])
                    # See if we need to shift the ExprRange to
                    # align start indices.
                    if _k == 0:
                        # Use the first start/end indices by convention.
                        start_index = entry.true_start_index
                        end_index = entry.true_end_index
                    else:
                        # Align indices to the first ExprTuple.
                        updater.update(updater.inner_expr()[idx].
                                       shift_equivalence(
                                               new_start=start_index,
                                               new_end=end_index))
                else:
                    assert min_entry_length == one
            idx += 1
        
        # Append to equations, reversed_equations (where requested)
        # and return the aligned ExprTuples.
        if equations is not None:
            for updater in trans_rel_updaters:
                equations.append(updater.relation)
        if reversed_equations is not None:
            for updater in trans_rel_updaters:
                reversed_equations.append(updater.relation.derive_reversed())
        return [updater.expr for updater in trans_rel_updaters]
                                          
    
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
