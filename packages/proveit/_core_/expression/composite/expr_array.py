import inspect
from .expr_tuple import ExprTuple
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.expression.style_options import StyleOptions


class ExprArray(ExprTuple):
    '''
    An ExprArray is simply an ExprTuple of ExprTuples or ExprRanges.
    The array is broken up into different rows after each ExprTuple
    or ExprRange. Each column MUST contain the same type of expression.
    '''

    def __init__(self, *expressions, styles=None):
        '''
        Initialize an ExprTuple from an iterable over Expression
        objects.
        '''
        from .expr_range import ExprRange
        ExprTuple.__init__(self, *expressions)

        for entry in self.entries:
            entry_or_body = entry
            while isinstance(entry_or_body, ExprRange):
                # May be a range of ranges of ExprTuples, etc.
                entry_or_body = entry_or_body.body
            if not isinstance(entry_or_body, ExprTuple):
                raise ValueError(
                    "Each element of an ExprRange must represent a tuple, "
                    "entries being tuples or ranges of tuples.")

        # check each column for same expression throughout
        self.check_range()

    @classmethod
    def _make(sub_class, core_info, sub_expressions):
        if sub_class != ExprArray:
            MakeNotImplemented(sub_class)
        if len(core_info) != 1 or core_info[0] != 'ExprTuple':
            raise ValueError("An ExprArray is an ExprTuple of ExprTuples, "
                             "so the ExprArray core_info should contain "
                             "exactly one item: 'ExprTuple'")
        return ExprArray(*sub_expressions)

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?  Return a
        tuple of strings with the calls to make.  The default for the
        Operation class is to include appropriate 'with_wrapping_at'
        and 'with_justification' calls.
        '''
        call_strs = []
        orientation = self.get_style('orientation')
        if orientation != 'horizontal':
            call_strs.append('with_orientation("' + orientation + '")')
        justification = self.get_style('justification')
        if justification != 'center':
            call_strs.append('with_justification("' + justification + '")')
        parameterization = self.get_style('parameterization', 'default')
        if parameterization != 'default':
            if parameterization == 'explicit':
                call_strs.append('with_explicit_parameterization()')
            if parameterization == 'implicit':
                call_strs.append('with_implicit_parameterization()')
        return call_strs

    def style_options(self):
        '''
        Return the StyleOptions object for this ExprArray.
        '''
        options = StyleOptions(self)
        options.add_option(
            name = 'justification',
            description = ("justify to the 'left', 'center', or 'right' "
                           "in the array cells"),
            default = 'center',
            related_methods = ('with_justification'))
        options.add_option(
            name = 'orientation',
            description = ("to be read from left to right then top to "
                           "bottom ('horizontal') or to be read top to "
                           "bottom then left to right ('vertical')"),
            default = 'horizontal',
            related_methods = ('with_orientation'))
        options.add_option(
            name = 'parameterization',
            description = (
                    "'implicit' (default for LaTeX formatting) hides "
                    "the parameter the ExprRange so the parameterization "
                    "may be ambiguous (e.g., x_{1+1}, ..., x_{n+1}); "
                    "'explicit' (default for string formatting) reveals "
                    "the parameterization "
                    "(e.g. x_{1+1}, ..x_{k+1}.., x_{n+1})."),
            default = None, # Removes the 'parameterization' key.
            related_methods = ('with_explicit_parameterization',
                               'with_implicit_parameterization',
                               'with_default_parameterization_style'))
        return options
    
    def with_justification(self, justification):
        return self.with_styles(justification=justification)

    def with_orientation(self, orientation):
        '''
        Wrap the expression according to the orientation: 'horizontal' or 'vertical'
        '''
        if orientation not in ('horizontal', 'vertical'):
            raise ValueError("'orientation' must be 'horizontal' or "
                             "'vertical', not %s" % orientation)
        return self.with_styles(orientation=orientation)

    def with_explicit_parameterization(self):
        '''
        The 'parameterization':'explicit' style shows the
        parameterization of the ExprRange explicitly.  For example,
        x_{1+1}, ..x_{k+1}.., x_{n+1}).
        '''
        return self.with_styles(parameterization='explicit')

    def with_implicit_parameterization(self):
        '''
        The 'parameterization':'implicit' style does not show the
        parameterization of the ExprRange explicitly and such that the
        parameterization may be ambiguous but is more compact.
        For example, x_{1+1}, ..., x_{n+1} could be
        x_{1+1}, ..x_{k+1}.., x_{n+1}
        or could be
        x_{1+1}, ..x_{k}.., x_{n+1}.
        '''
        return self.with_styles(parameterization='implicit')

    def with_default_parameterization_style(self):
        '''
        The default is to use an 'implicit' parameterization for
        string formatting (see 'with_implicit_parameterization') and
        and 'explicit' parameterization for LaTeX formatting
        (see 'with_explicit_parameterization').
        '''
        return self.with_default_style('parameterization')

    def flat(self):
        '''
        Returns the contents of the array as a flattened ExprTuple.
        For example, instead of returning [[A, B, C}, [D, E, F]] - which displays as
         A B C
         D E F
        it would return [A, B, C, D, E, F]
        '''
        output = ExprTuple()
        for entry in self:
            if isinstance(entry, ExprTuple):
                for value in entry:
                    print(value)
                    output = output.__add__([value])
            else:
                print(entry)
                output = output.__add__([entry])

        return output

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def check_range(self):
        '''
        If there is an ExprRange contained in the array,
        every item in the same column MUST agree in length
        of the ExprRange.  If not, raise an error.
        '''
        from .expr_range import ExprRange
        from proveit.physics.quantum.circuit import MultiQubitGate, Gate
        pos = []

        k = 0
        for m, expr in enumerate(self):
            if isinstance(expr, ExprTuple):
                count = 0
                for i, entry in enumerate(expr):
                    if isinstance(entry, ExprRange):

                        if isinstance(
                                entry.first(),
                                MultiQubitGate) or isinstance(
                                entry.first(),
                                Gate):
                            # we break in this instance because we have a check
                            # in Circuit
                            return
                        if m == 0:
                            placeholder = []
                            placeholder.append(i)
                            placeholder.append(entry.start_index)
                            placeholder.append(entry.end_index)
                            pos.append(placeholder)
                        else:
                            if len(pos) == 0:
                                raise ValueError(
                                    'There is an invalid ExprRange in tuple number %s' % str(i))
                            for item in pos:
                                if item[0] == i:
                                    if entry.start_index != item[1]:
                                        raise ValueError(
                                            'Columns containing ExprRanges '
                                            'must agree for every row. %s from %s is '
                                            'not equal to %s.' %
                                            (entry.start_index, entry, item[1]))
                                    if entry.end_index != item[2]:
                                        raise ValueError(
                                            'Columns containing ExprRanges '
                                            'must agree for every row. %s from %s is '
                                            'not equal to %s.' %
                                            (entry.end_index, entry, item[2]))
                                    k += 1
                        count += 3
                    else:
                        count += 1

                if count != self.get_row_length():
                    raise ValueError(
                        'One or more rows are a different length.  Please double check your entries.')
            elif isinstance(expr, ExprRange):
                if isinstance(expr.first(), ExprTuple):
                    first = None
                    last = None
                    for i, entry in enumerate(expr.first()):

                        if isinstance(entry, ExprTuple):
                            raise ValueError(
                                'Nested ExprTuples are not supported. Fencing is an '
                                'extraneous feature for the ExprArray class.')
                        elif isinstance(entry, ExprRange):
                            if isinstance(
                                    entry.first(),
                                    MultiQubitGate) or isinstance(
                                    entry.first(),
                                    Gate):
                                # we break in this instance because we have a
                                # check in Circuit
                                return

                            if m == 0:
                                # we are checking that i in Aij matches all the
                                # other i's
                                placeholder = []
                                placeholder.append(i)
                                placeholder.append(entry.first().indices[1])
                                placeholder.append(entry.last().indices[1])
                                pos.append(placeholder)
                            if first is None:
                                first = entry.first().indices[0]
                            if first != entry.first().indices[0]:
                                raise ValueError(
                                    'Rows containing ExprRanges must agree for every column. %s from %s '
                                    'is not equal to %s.' %
                                    (first, entry.first(), entry.first().indices[0]))

                        else:
                            if isinstance(
                                    entry,
                                    MultiQubitGate) or isinstance(
                                    entry,
                                    Gate):
                                # we break in this instance because we have a
                                # check in Circuit
                                return
                            if first is None:
                                first = entry.indices[0]
                            if first != entry.indices[0]:
                                raise ValueError(
                                    'Rows containing ExprRanges must agree for every column. %s from %s '
                                    'is not equal to %s.' %
                                    (first, entry, entry.indices[0]))
                    for entry in expr.last():
                        if isinstance(entry, ExprTuple):
                            raise ValueError(
                                'Nested ExprTuples are not supported. Fencing is an '
                                'extraneous feature for the ExprArray class.')
                        elif isinstance(entry, ExprRange):
                            if isinstance(
                                    entry.first(),
                                    MultiQubitGate) or isinstance(
                                    entry,
                                    Gate):
                                # we break in this instance because we have a
                                # check in Circuit
                                return
                            if last is None:
                                last = entry.last().indices[0]
                            if last != entry.last().indices[0]:
                                raise ValueError(
                                    'Rows containing ExprRanges must agree for every column. %s from %s '
                                    'is not equal to %s.' %
                                    (last, entry.last(), entry.last().indices[0]))

                        else:
                            if isinstance(
                                    entry,
                                    MultiQubitGate) or isinstance(
                                    entry,
                                    Gate):
                                # we break in this instance because we have a
                                # check in Circuit
                                return
                            if last is None:
                                last = entry.indices[0]
                            if last != entry.indices[0]:
                                raise ValueError(
                                    'Rows containing ExprRanges must agree for every column. %s from %s '
                                    'is not equal to %s.' %
                                    (last, entry, entry.indices[0]))
            n = m

        if k != len(pos):
            if n == 0:
                pass
            else:
                raise ValueError(
                    'The ExprRange in the first tuple is not in the same column '
                    'as the ExprRange in tuple number %s' %
                    str(n))

    def get_col_height(self, explicit=False):
        '''
        Return the height of the first column of the array in an integer form.
        (Horizontal orientation is assumed)
        '''
        from .expr_range import ExprRange
        output = 0
        for expr in self:
            if isinstance(expr, ExprTuple):
                output += 1
            elif isinstance(expr, ExprRange):
                if isinstance(expr.first(), ExprRange):
                    if explicit:
                        output += 7
                    else:
                        output += 8
                else:
                    output += 3
        return output

    def get_row_length(self, explicit=False):
        '''
        Return the length of the first row of the array in an integer form.
        (Horizontal orientation is assumed)
        '''
        from .expr_range import ExprRange
        from proveit import Variable, IndexedVar
        output = 0

        for expr in self:
            if isinstance(expr, ExprRange):
                if isinstance(expr.first(), ExprRange):
                    if isinstance(expr.first().first(), ExprTuple):
                        for value in expr.first().first():
                            output += 1
                elif isinstance(expr.first(), ExprTuple):
                    for value in expr.first():
                        if isinstance(value, ExprTuple):
                            for var in value:
                                if isinstance(
                                        var, Variable) or isinstance(
                                        var, IndexedVar):
                                    output += 1
                                elif isinstance(value, ExprTuple):
                                    for operand in value:
                                        if isinstance(
                                                operand, ExprRange) or isinstance(
                                                operand, ExprTuple):
                                            raise ValueError(
                                                'This expression is nested too many times to get an '
                                                'accurate row length. Please consolidate your ExprRange')
                                        else:
                                            output += 1
                        elif isinstance(value, ExprRange):
                            if explicit:
                                output += 5
                            else:
                                output += 3
                        else:
                            output += 1
            if isinstance(expr, ExprTuple):
                for value in expr:
                    if isinstance(value, ExprTuple):
                        for var in value:
                            if isinstance(var, ExprTuple):
                                for operand in value:
                                    if isinstance(
                                            operand, ExprRange) or isinstance(
                                            operand, ExprTuple):
                                        raise ValueError(
                                            'This expression is nested too many times to get an '
                                            'accurate row length. Please consolidate your ExprTuple')
                                    else:
                                        output += 1
                            else:
                                output += 1
                    elif isinstance(value, ExprRange):
                        if explicit:
                            output += 5
                        else:
                            output += 3
                    else:
                        output += 1
            break
        return output

    def get_formatted_sub_expressions(
            self,
            format_type,
            orientation,
            default_style,
            operator_or_operators):
        '''
        Used to cycle through the ExprArray and format the output accordingly
        '''
        from .expr_range import ExprRange

        # Track whether or not ExprRange operands are using
        # "explicit" parameterization, because the operators must
        # follow suit.
        using_explicit_parameterization = []
        for k, sub_expr in enumerate(self):
            if k != 0 and orientation == 'horizontal':
                # wrap before each expression, excluding the first.
                yield r' \\' + ' \n '
            if isinstance(sub_expr, ExprRange):
                # Handle an ExprRange entry; here the "sub-expressions"
                # are really ExprRange "checkpoints" (first, last, as
                # well as the ExprRange body in the middle if using
                # an 'explicit' style for 'parameterization) as well as
                # ellipses between the checkpoints..
                using_explicit_parameterization.append(
                    sub_expr._use_explicit_parameterization(format_type))

                ell = []
                vell = []
                # ell will be used to store the vertical ellipses
                # for the horizontal orientation while vell will store
                # the horizontal ellipses for the vertical orientation
                for i, expr in enumerate(sub_expr._formatted_checkpoints(
                        format_type, fence=False, sub_fence=False, operator=operator_or_operators)):
                    # if orientation is 'vertical' replace all \vdots with
                    # \cdots and vice versa.
                    if i == 0 and isinstance(sub_expr.first(), ExprTuple):
                        # only do this once, right away
                        for m, entry in enumerate(sub_expr.first().entries):
                            if m == 0:
                                # for the first entry, don't include '&' for
                                # formatting purposes
                                if isinstance(entry, ExprTuple):
                                    for n, var in enumerate(entry):
                                        if n != 0:
                                            if orientation == 'horizontal':
                                                yield '& ' + var.formatted(format_type, solo=False, fence=False)
                                                if self.get_style(
                                                        'parameterization', default_style) == 'explicit':
                                                    ell.append(r'& \colon')
                                                else:
                                                    ell.append(r'& \vdots')
                                            else:
                                                # if the orientation is
                                                # 'vertical', include the
                                                # ellipses
                                                if k == 0:
                                                    yield var.formatted(format_type, solo=False, fence=False)
                                                    vell.append(r'& \cdots')
                                                else:
                                                    yield '& ' + var.formatted(format_type, solo=False, fence=False)
                                                    vell.append(r'& \cdots')
                                        else:
                                            # for the first entry, don't
                                            # include '&' for formatting
                                            # purposes

                                            if orientation == 'horizontal':
                                                yield var.formatted(format_type, solo=False, fence=False)
                                                if self.get_style(
                                                        'parameterization', default_style) == 'explicit':
                                                    ell.append(r'\colon')
                                                else:
                                                    ell.append(r'\vdots')
                                            else:
                                                # if the orientation is
                                                # 'vertical', include the
                                                # ellipses
                                                if k == 0:
                                                    yield var.formatted(format_type, solo=False, fence=False)
                                                    vell.append(r'& \cdots')
                                                else:
                                                    yield '& ' + var.formatted(format_type, solo=False, fence=False)
                                                    vell.append(r'& \cdots')
                                elif isinstance(entry, ExprRange):
                                    # this is first for both orientations so
                                    # don't include the '&' for either
                                    using_explicit_parameterization.append(
                                        entry._use_explicit_parameterization(format_type))
                                    yield entry.first().formatted(format_type, solo=False, fence=False)
                                    if orientation == 'horizontal':
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':

                                            yield '& ..' + entry.body.formatted(format_type, solo=False, fence=False) \
                                                  + '..'
                                            ell.append(r'\colon')
                                            ell.append(r'& \colon')
                                            ell.append(r'& \colon')
                                        else:
                                            yield r'& \cdots'
                                            ell.append(r'\vdots')

                                            ell.append('& ' + sub_expr.body.entries[m].body.formatted(format_type,
                                                                                                      solo=False,
                                                                                                      fence=False))
                                            ell.append(r'& \vdots')

                                        yield '& ' + entry.last().formatted(format_type, solo=False, fence=False)
                                    else:
                                        # we add an '&' after the \vdots
                                        # because this is a range of a tuple of
                                        # a range
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            yield r'\colon'
                                            yield entry.body.formatted(format_type, solo=False, fence=False)
                                            yield r'\colon'
                                        else:
                                            yield r'\vdots'
                                        vell.append(r'& \cdots')

                                        vell.append('& ' + sub_expr.body.entries[m].body.formatted(format_type,
                                                                                                   solo=False,
                                                                                                   fence=False))

                                        yield entry.last().formatted(format_type, solo=False, fence=False)
                                        vell.append(r'& \cdots')
                                else:
                                    if orientation == 'horizontal':
                                        yield entry.formatted(format_type, solo=False, fence=False)
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            ell.append(r'\colon')
                                        else:
                                            ell.append(r'\vdots')
                                    else:
                                        # if the orientation is 'vertical',
                                        # include the ellipses
                                        if k == 0:
                                            yield entry.formatted(format_type, solo=False, fence=False)
                                            vell.append(r'& \cdots')
                                        else:
                                            yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                            vell.append(r'& \cdots')
                            else:
                                if isinstance(entry, ExprTuple):
                                    for var in entry:
                                        if orientation == 'horizontal':
                                            # this is not the first so we add
                                            # '&'
                                            yield '& ' + var.formatted(format_type, solo=False, fence=False)
                                            if self.get_style(
                                                    'parameterization', default_style) == 'explicit':
                                                ell.append(r'& \colon')
                                            else:
                                                ell.append(r'& \vdots')
                                        else:
                                            if k == 0:
                                                # this is still technically the first column so we don't include
                                                # the '&' for formatting
                                                # purposes
                                                yield var.formatted(format_type, solo=False, fence=False)
                                                vell.append(r'& \cdots')
                                            else:
                                                yield '& ' + var.formatted(format_type, solo=False, fence=False)
                                                vell.append(r'& \cdots')
                                elif isinstance(entry, ExprRange):
                                    using_explicit_parameterization.append(
                                        entry._use_explicit_parameterization(format_type))
                                    if orientation == 'horizontal':
                                        yield '& ' + entry.first().formatted(format_type, solo=False, fence=False)
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            ell.append(r'& \colon')
                                            ell.append(r'& \colon')
                                            ell.append(r'& \colon')
                                            yield '& ..' + entry.body.formatted(format_type, solo=False,
                                                                                fence=False) + '..'
                                        else:
                                            ell.append(r'& \vdots')
                                            ell.append(
                                                r'& ' +
                                                sub_expr.body.entries[m].body.formatted(format_type,
                                                                                        solo=False,
                                                                                        fence=False))
                                            ell.append(r'& \vdots')
                                            yield r'& \cdots'
                                        yield '& ' + entry.last().formatted(format_type, solo=False, fence=False)

                                    else:
                                        # this is still technically the first column so we don't include
                                        # the '&' for formatting purposes
                                        yield entry.first().formatted(format_type, solo=False, fence=False)

                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            yield r'\colon'
                                            yield entry.body.formatted(format_type, solo=False, fence=False)
                                            yield r'\colon'
                                        else:
                                            yield r'\vdots'
                                        yield entry.last().formatted(format_type, solo=False, fence=False)
                                        vell.append(r'& \cdots ')
                                        vell.append(
                                            '& ' +
                                            sub_expr.body.entries[m].body.formatted(format_type, solo=False,
                                                                                    fence=False))
                                        vell.append(r'& \cdots ')
                                else:
                                    if orientation == 'horizontal':
                                        # this is not the first so we add '&'
                                        yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            ell.append(r'& \colon')
                                        else:
                                            ell.append(r'& \vdots')
                                    else:
                                        if k == 0:
                                            # this is still technically the first column so we don't include
                                            # the '&' for formatting purposes
                                            yield entry.formatted(format_type, solo=False, fence=False)
                                            vell.append(r'& \cdots')
                                        else:
                                            yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                            vell.append(r'& \cdots')

                    elif (expr == sub_expr.last().formatted(format_type, solo=False, fence=False)) \
                            and isinstance(sub_expr.last(), ExprTuple):
                        # if orientation is 'horizontal' this is the last row
                        # if orientation is 'vertical' this is the last column
                        for m, entry in enumerate(sub_expr.last().entries):
                            if m == 0:
                                if isinstance(entry, ExprTuple):
                                    n = 0
                                    for var in entry:
                                        if n != 0:
                                            # regardless of orientation add the
                                            # '&'
                                            yield '& ' + var.formatted(format_type, solo=False, fence=False)
                                        else:
                                            if orientation == 'horizontal':
                                                # if its the first one, omit
                                                # '&' for formatting purposes
                                                yield var.formatted(format_type, solo=False, fence=False)
                                            else:
                                                # add the '&' because this is
                                                # technically the last column
                                                yield '& ' + var.formatted(format_type, solo=False, fence=False)
                                        n += 1
                                elif isinstance(sub_expr.last().entries[0], ExprRange):
                                    using_explicit_parameterization.append(
                                        entry._use_explicit_parameterization(format_type))
                                    if orientation == 'horizontal':
                                        # this is the first of the last row so
                                        # we omit the '&'
                                        yield entry.first().formatted(format_type, solo=False, fence=False)
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            yield r'& ..' + entry.body.formatted(format_type, solo=False,
                                                                                 fence=False) + '..'
                                        else:
                                            yield r'& \cdots'
                                        yield '& ' + entry.last().formatted(format_type, solo=False, fence=False)
                                    else:
                                        # this is the last column so we include
                                        # all '&'
                                        yield '& ' + entry.first().formatted(format_type, solo=False, fence=False)
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            yield r'& \colon'
                                            yield '& ' + entry.body.formatted(format_type, solo=False, fence=False)
                                            yield r'& \colon'
                                        else:
                                            yield r'& \vdots'
                                        yield '& ' + entry.last().formatted(format_type, solo=False, fence=False)
                                else:
                                    if orientation == 'horizontal':
                                        yield entry.formatted(format_type, solo=False, fence=False)
                                    else:
                                        yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                            else:
                                if isinstance(entry, ExprTuple):
                                    for var in entry:
                                        # this is not the first entry for
                                        # either orientation so we include an
                                        # '&'
                                        yield '& ' + var.formatted(format_type, solo=False, fence=False)

                                elif isinstance(entry, ExprRange):
                                    using_explicit_parameterization.append(
                                        entry._use_explicit_parameterization(format_type))
                                    # this is not the first entry for either
                                    # orientation so we include an '&'
                                    yield '& ' + entry.first().formatted(format_type, solo=False, fence=False)

                                    if self.get_style(
                                            'parameterization', default_style) == 'explicit':
                                        if orientation == 'horizontal':
                                            yield r'& ..' + entry.body.formatted(format_type, solo=False, fence=False) \
                                                  + '..'
                                        else:
                                            yield r'& \colon'
                                            yield '& ' + entry.body.formatted(format_type, solo=False, fence=False)
                                            yield r'& \colon'
                                    else:
                                        if orientation == 'horizontal':
                                            yield r'& \cdots'
                                        else:
                                            yield r'& \vdots'
                                    yield '& ' + entry.last().formatted(format_type, solo=False, fence=False)
                                else:
                                    # this is not the first entry for either
                                    # orientation so we include an '&'
                                    yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                    elif i == 1 and isinstance(sub_expr.first(), ExprTuple):
                        if self.get_style(
                            'parameterization',
                                default_style) == 'explicit':
                            if orientation == 'horizontal':
                                yield r' \\ ' + '\n '
                                for entry in ell:
                                    yield entry
                                yield r' \\ ' + '\n '
                                for n, entry in enumerate(sub_expr.body):
                                    if n == 0:
                                        if isinstance(entry, ExprRange):
                                            yield entry.first().formatted(format_type, solo=False, fence=False)
                                            yield '& ..' + entry.body.formatted(format_type, solo=False,
                                                                                fence=False) + '..'
                                            yield '& ' + entry.last().formatted(format_type, solo=False, fence=False)
                                        else:
                                            yield entry.formatted(format_type, solo=False, fence=False)
                                    else:
                                        if isinstance(entry, ExprRange):
                                            yield '& ' + entry.first().formatted(format_type, solo=False, fence=False)
                                            yield '& ..' + entry.body.formatted(format_type, solo=False,
                                                                                fence=False) + '..'
                                            yield '& ' + entry.last().formatted(format_type, solo=False, fence=False)
                                        else:
                                            yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                yield r' \\ ' + '\n '
                                for entry in ell:
                                    yield entry
                                yield r' \\ ' + '\n '
                            else:
                                for entry in sub_expr.body:
                                    if isinstance(entry, ExprRange):
                                        yield '& ..' + entry.first().formatted(format_type, solo=False,
                                                                               fence=False) + '..'
                                        yield r'& \colon'
                                        yield '& ..' + entry.body.formatted(format_type, solo=False, fence=False) \
                                              + '..'
                                        yield r'& \colon'
                                        yield '& ..' + entry.last().formatted(format_type, solo=False, fence=False) \
                                              + '..'
                                    else:
                                        yield '& ..' + entry.formatted(format_type, solo=False, fence=False) + '..'
                        else:
                            if orientation == 'horizontal':
                                yield r' \\ ' + '\n '
                                for entry in ell:
                                    yield entry
                                yield r' \\ ' + '\n '
                            else:
                                for entry in vell:
                                    yield entry
                    elif isinstance(sub_expr.first(), ExprRange):
                        # ExprRange of an ExprRange
                        if isinstance(sub_expr.first().first(), ExprTuple):
                            # ExprRange of an ExprRange of an ExprTuple
                            if i == 0:
                                # we just want to do this once
                                ell = []
                                vell = []
                                for n, entry in enumerate(
                                        sub_expr.first().first()):
                                    if n == 0:
                                        yield entry.formatted(format_type, solo=False, fence=False)
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            vell.append(r'\colon')
                                        else:
                                            vell.append(r'\vdots')
                                            ell.append(r'& \cdots')

                                    else:
                                        if orientation == 'horizontal':
                                            yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                        else:
                                            yield entry.formatted(format_type, solo=False, fence=False)
                                        if self.get_style(
                                                'parameterization', default_style) == 'explicit':
                                            vell.append(r'& \colon')
                                        else:
                                            vell.append(r'& \vdots')
                                            ell.append(r'& \cdots')
                                if orientation == 'horizontal':
                                    yield r' \\ ' + '\n '
                                    for entry in vell:
                                        yield entry
                                    yield r' \\ ' + '\n '
                                else:
                                    for item in ell:
                                        yield item

                                if self.get_style(
                                        'parameterization', default_style) == 'explicit':
                                    for n, entry in enumerate(
                                            sub_expr.first().body):
                                        if n == 0 and orientation == 'horizontal':
                                            yield entry.formatted(format_type, solo=False, fence=False)
                                        else:
                                            if orientation == 'horizontal':
                                                yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                            else:
                                                yield '& ..' + entry.formatted(format_type, solo=False, fence=False) \
                                                      + '..'
                                    if orientation == 'horizontal':
                                        yield r' \\ ' + '\n '
                                        for entry in vell:
                                            yield entry
                                        yield r' \\ ' + '\n '
                                    else:
                                        for item in ell:
                                            yield item
                                for n, entry in enumerate(
                                        sub_expr.first().last()):
                                    if n == 0 and orientation == 'horizontal':
                                        yield entry.formatted(format_type, solo=False, fence=False)
                                    else:
                                        yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                if orientation == 'horizontal':
                                    yield r' \\ ' + '\n '
                                    for entry in vell:
                                        yield entry
                                    yield r' \\ ' + '\n '
                                    if self.get_style(
                                            'parameterization', default_style) == 'explicit':
                                        for entry in vell:
                                            yield entry
                                        yield r' \\ ' + '\n '
                                        for n, entry in enumerate(
                                                sub_expr.body.first()):
                                            if n == 0:
                                                yield entry.formatted(format_type, solo=False, fence=False)
                                            else:
                                                yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                        yield r' \\ ' + '\n '
                                        for entry in vell:
                                            yield entry
                                        yield r' \\ ' + '\n '
                                        for n, entry in enumerate(
                                                sub_expr.body.body):
                                            if n == 0:
                                                yield entry.formatted(format_type, solo=False, fence=False)
                                            else:
                                                yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                        yield r' \\ ' + '\n '
                                        for entry in vell:
                                            yield entry
                                        yield r' \\ ' + '\n '
                                        for n, entry in enumerate(
                                                sub_expr.body.last()):
                                            if n == 0:
                                                yield entry.formatted(format_type, solo=False, fence=False)
                                            else:
                                                yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                        yield r' \\ ' + '\n '
                                        for entry in vell:
                                            yield entry
                                        yield r' \\ ' + '\n '

                                    for entry in vell:
                                        yield entry
                                    yield r' \\ ' + '\n '
                                else:
                                    if self.get_style(
                                            'parameterization', default_style) == 'explicit':
                                        for n, entry in enumerate(
                                                sub_expr.body.first()):
                                            placeholder = ''
                                            placeholder += '& ....' + sub_expr.body.first().entries[n].formatted(
                                                format_type, solo=False, fence=False)
                                            placeholder += '..' + sub_expr.body.body.entries[n].formatted(
                                                format_type, solo=False, fence=False)
                                            placeholder += '..' + sub_expr.body.last().entries[n].formatted(
                                                format_type, solo=False, fence=False) + '....'
                                            yield placeholder
                                    else:
                                        for item in ell:
                                            yield item
                                            yield item
                                for n, entry in enumerate(
                                        sub_expr.last().first()):
                                    if n == 0 and orientation == 'horizontal':
                                        yield entry.formatted(format_type, solo=False, fence=False)
                                    else:
                                        yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                if orientation == 'horizontal':
                                    yield r' \\ ' + '\n '
                                    for entry in vell:
                                        yield entry
                                    yield r' \\ ' + '\n '
                                else:
                                    for item in ell:
                                        yield item
                                if self.get_style(
                                        'parameterization', default_style) == 'explicit':
                                    for n, entry in enumerate(
                                            sub_expr.last().body):
                                        if n == 0 and orientation == 'horizontal':
                                            yield entry.formatted(format_type, solo=False, fence=False)
                                        else:
                                            if orientation == 'horizontal':
                                                yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                                            else:
                                                yield '& ..' + entry.formatted(format_type, solo=False,
                                                                               fence=False) + '..'
                                    if orientation == 'horizontal':
                                        yield r' \\ ' + '\n '
                                        for entry in vell:
                                            yield entry
                                        yield r' \\ ' + '\n '
                                    else:
                                        for item in ell:
                                            yield item
                                for n, entry in enumerate(
                                        sub_expr.last().last()):
                                    if n == 0 and orientation == 'horizontal':
                                        yield entry.formatted(format_type, solo=False, fence=False)
                                    else:
                                        yield '& ' + entry.formatted(format_type, solo=False, fence=False)
                        else:
                            raise ValueError(
                                'ExprArrays of ExprRanges of ExprRanges are one-dimensional and therefore '
                                'not valid ExprArrays.  Please wrap either the second ExprRange in an '
                                'ExprTuple or place an ExprTuple in the second ExprRange.')
                    i += 1
            elif isinstance(sub_expr, ExprTuple):
                # always fence nested expression lists
                for inc, expr in enumerate(sub_expr):
                    if inc == 0:
                        # for the first instance, we don't include '&' for
                        # formatting purposes
                        if isinstance(expr, ExprRange):
                            using_explicit_parameterization.append(
                                expr._use_explicit_parameterization(format_type))
                            if orientation == 'horizontal':
                                yield expr.first().formatted(format_type, solo=False, fence=False, sub_fence=False)
                                if self.get_style(
                                        'parameterization', default_style) == 'explicit':
                                    yield r'& ..' + expr.body.formatted(format_type, solo=False, fence=False,
                                                                        sub_fence=False) + '..'
                                else:
                                    yield r'& \cdots'
                                yield '& ' + expr.last().formatted(format_type, solo=False, fence=False,
                                                                   sub_fence=False)
                            else:
                                if k == 0:
                                    # this is the first column so we don't
                                    # include '&'
                                    yield expr.first().formatted(format_type, solo=False, fence=False,
                                                                 sub_fence=False)
                                    if self.get_style(
                                            'parameterization', default_style) == 'explicit':
                                        yield r'\colon'
                                        yield expr.body.formatted(format_type, solo=False, fence=False,
                                                                  sub_fence=False)
                                        yield r'\colon'
                                    else:
                                        yield r'\vdots'
                                    yield expr.last().formatted(format_type, solo=False, fence=False,
                                                                sub_fence=False)
                                else:
                                    yield '& ' + expr.first().formatted(format_type, solo=False, fence=False,
                                                                        sub_fence=False)
                                    if self.get_style(
                                            'parameterization', default_style) == 'explicit':
                                        yield r'& \colon'
                                        yield r'& ' + expr.body.formatted(format_type, solo=False, fence=False,
                                                                          sub_fence=False)
                                        yield r'& \colon'
                                    else:
                                        yield r'& \vdots'
                                    yield '& ' + expr.last().formatted(format_type, solo=False, fence=False,
                                                                       sub_fence=False)
                        else:
                            if orientation == 'horizontal':
                                # this is the first item in the first row so we
                                # do not include the '&'
                                yield expr.formatted(format_type, solo=False, fence=False)
                            else:
                                if k == 0:
                                    # this is still the first column
                                    yield expr.formatted(format_type, solo=False, fence=False, sub_fence=False)
                                else:
                                    # this is not the first column
                                    yield '& ' + expr.formatted(format_type, solo=False, fence=False, sub_fence=False)
                    else:
                        if isinstance(expr, ExprRange):
                            using_explicit_parameterization.append(
                                expr._use_explicit_parameterization(format_type))
                            if orientation == 'horizontal':
                                # for this orientation this is not the first so
                                # we add '&'
                                yield '& ' + expr.first().formatted(format_type, solo=False, fence=False,
                                                                    sub_fence=False)
                                if self.get_style(
                                        'parameterization', default_style) == 'explicit':
                                    yield r'& ..' + expr.body.formatted(format_type, solo=False, fence=False,
                                                                        sub_fence=False) + '..'
                                else:
                                    yield r'& \cdots'
                                yield '& ' + expr.last().formatted(format_type, solo=False, fence=False,
                                                                   sub_fence=False)
                            else:
                                if k == 0:
                                    # this is still the first column so we
                                    # don't add '&'
                                    yield expr.first().formatted(format_type, solo=False, fence=False,
                                                                 sub_fence=False)
                                    if self.get_style(
                                            'parameterization', default_style) == 'explicit':
                                        yield r'\colon'
                                        yield expr.body.formatted(format_type, solo=False, fence=False,
                                                                  sub_fence=False)
                                        yield r'\colon'
                                    else:
                                        yield r'\vdots'
                                    yield expr.last().formatted(format_type, solo=False, fence=False,
                                                                sub_fence=False)
                                else:
                                    yield '& ' + expr.first().formatted(format_type, solo=False, fence=False,
                                                                        sub_fence=False)
                                    if self.get_style(
                                            'parameterization', default_style) == 'explicit':
                                        yield r'& \colon'
                                        yield '& ' + expr.body.formatted(format_type, solo=False, fence=False,
                                                                         sub_fence=False)
                                        yield r'& \colon'
                                    else:
                                        yield r'& \vdots'
                                    yield '& ' + expr.last().formatted(format_type, solo=False, fence=False,
                                                                       sub_fence=False)
                        else:
                            if orientation == 'horizontal':
                                # this is following along the row so we include
                                # '&'
                                yield '& ' + expr.formatted(format_type, solo=False, fence=False)
                            else:
                                if k == 0:
                                    # this is the first column so we don't
                                    # include '&'
                                    yield expr.formatted(format_type, solo=False, fence=False, sub_fence=False)
                                else:
                                    # this is not the first column so we do
                                    # include '&'
                                    yield '& ' + expr.formatted(format_type, solo=False, fence=False, sub_fence=False)
            else:
                raise ValueError(
                    "Expressions must be wrapped in either an ExprTuple or ExprRange")

    def formatted(
            self,
            format_type,
            fence=False,
            sub_fence=False,
            operator_or_operators=None,
            implicit_first_operator=False,
            wrap_positions=None,
            justification=None,
            orientation=None,
            **kwargs):
        from .expr_range import ExprRange
        default_style = ("explicit" if format_type == 'string' else 'implicit')

        out_str = ''
        if len(self.entries) == 0 and fence:
            # for an empty list, show the parenthesis to show something.
            return '()'

        if justification is None:
            justification = self.get_style('justification', 'center')
        if orientation is None:
            orientation = self.get_style('orientation', 'horizontal')

        if fence:
            out_str = '(' if format_type == 'string' else r'\left('

        if orientation == 'horizontal':
            length = self.get_row_length()
        else:
            if self.get_style('parameterization', default_style):
                length = self.get_col_height(True)
            else:
                length = self.get_col_height()
        if format_type == 'latex':
            out_str += r'\begin{array} {%s} ' % (
                justification[0] * length) + '\n '

        formatted_sub_expressions = []

        for entry in self.get_formatted_sub_expressions(
                format_type, orientation, default_style, operator_or_operators):
            formatted_sub_expressions.append(entry)

        if orientation == "vertical":
            # up until now, the formatted_sub_expression is still
            # in the order of the horizontal orientation regardless of
            # orientation type
            k = 1
            vert = []
            if self.get_style('parameterization', default_style) == 'explicit':
                ex = True
            else:
                ex = False
            m = self.get_col_height(ex)
            while k <= self.get_row_length(ex):
                i = 1
                j = k
                for var in self.get_formatted_sub_expressions(
                        format_type, orientation, default_style, operator_or_operators):
                    if i == j:
                        vert.append(var)
                        m -= 1
                        if m == 0:
                            vert.append(r' \\' + ' \n ')
                            m = self.get_col_height(ex)
                        j += self.get_row_length(ex)
                    i += 1
                k += 1
            formatted_sub_expressions = vert

        if operator_or_operators is None:
            operator_or_operators = ','
        elif isinstance(operator_or_operators, Expression) and not isinstance(operator_or_operators, ExprTuple):
            operator_or_operators = operator_or_operators.formatted(
                format_type, fence=False)
        if isinstance(operator_or_operators, str):
            # single operator
            formatted_operator = operator_or_operators
            if operator_or_operators == ',':
                # e.g.: a, b, c, d
                out_str += (' ').join(formatted_sub_expressions)
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
                    be_explicit = self.get_style(
                        'parameterization', default_style)
                    formatted_operators += operator._formatted_checkpoints(
                        format_type, fence=False, sub_fence=False, ellipses='',
                        use_explicit_parameterization=be_explicit)
                else:
                    formatted_operators.append(operator.formatted(
                        format_type, fence=False, sub_fence=False))
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
                out_str += ' '.join(
                    formatted_operator + ' ' + formatted_operand for formatted_operator, formatted_operand in
                    zip(formatted_operators[1:], formatted_sub_expressions[1:]))
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
                raise ValueError(
                    "May only perform ExprTuple formatting if the number of operators is equal to the number "
                    "of operands(precedes each operand) or one less (between each operand); "
                    "also, operator ranges must be in correspondence with operand ranges.")

        if format_type == 'latex':
            out_str += r' \end{array}' + ' \n'
        if fence:
            out_str += ')' if format_type == 'string' else r'\right)'
        return out_str
