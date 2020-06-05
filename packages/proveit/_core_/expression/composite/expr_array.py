import types
from .composite import Composite, _simplifiedCoord
from .expr_tuple import ExprTuple
from proveit._core_.expression.expr import Expression, MakeNotImplemented
from proveit._core_.proof import ProofFailure
from proveit._core_.defaults import USE_DEFAULTS
from proveit._core_.expression.style_options import StyleOptions


class ExprArray(ExprTuple):
    '''
    An ExprArray is simply an ExprTuple of ExprTuples.
    '''
    def __init__(self, *expressions, styles=None):
        '''
        Initialize an ExprTuple from an iterable over Expression
        objects.
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
            assert isinstance(entry, Expression)
            entries.append(entry)
        self.entries = tuple(entries)
        self._lastEntryCoordInfo = None
        self._lastQueriedEntryIndex = 0

        if styles is None: styles = dict()
        if 'wrapPositions' not in styles:
            styles['wrapPositions'] = '()' # no wrapping by default
        if 'justification' not in styles:
            styles['justification'] = 'center'
        if 'orientation' not in styles:
            styles['orientation'] = 'horizontal'

        Expression.__init__(self, ['ExprTuple'], self.entries, styles=styles)

    def styleOptions(self):
        options = StyleOptions(self)
        options.addOption('wrapPositions',
                          ("position(s) at which wrapping is to occur; 'n' "
                           "is after the nth comma."))
        options.addOption('justification',
                          ("if any wrap positions are set, justify to the 'left', "
                           "'center', or 'right'"))
        options.addOption('orientation',
                          ("to be read from left to right then top to bottom ('horizontal') "
                           "or to be read top to bottom then left to right ('vertical')"))
        return options

    def wrapPositions(self):
        '''
        Return a list of wrap positions according to the current style setting.
        Position 'n' is after the nth comma.
        '''
        return [int(pos_str) for pos_str in self.getStyle('wrapPositions').strip('()').split(' ') if pos_str != '']

    def orientation(self, *wrap):
        '''
        Return a list of wrap positions according to the current style setting.
        Position 'n' is after the nth comma.
        '''

        return self.withWrappingAt(*wrap)

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def getFormattedList(self, formatType='latex', list=[]):
        '''
        Take an expression, nested or not, and return a list with each individual entry.
        Ellipsis for ExprRange and other similar types are denoted by 'ellipsis'.
        '''
        from .expr_range import ExprRange
        newList =[]
        print('top 85 ' + str(list))
        if list == []:
            if isinstance(self, ExprRange):
                list.append(self.first())
                list.append('ellipsis')
                list.append(self.last())
            elif isinstance(self, ExprTuple):
                for entry in self:
                    list.append(entry)
            elif isinstance(self, ExprArray):
                for entry in self:
                    list.append(entry)
            else:
                list.append(self)
            print('98 ' + str(list))
            return self.getFormattedList(formatType, list)
        count = 0
        for entry in list:
            if isinstance(entry, ExprRange):
                newList.append(entry.first())
                newList.append('ellipsis')
                newList.append(entry.last())
            elif isinstance(entry, ExprTuple):
                for value in entry:
                    newList.append(value)
            else:
                count += 1
                newList.append(entry)
        print(count)
        print(len(newList))
        print(count==len(newList))
        print(newList)
        if count==len(newList):
            lastlist=[]
            for entry in newList:
                print('entry 120 ' + str(entry))
                if isinstance(entry, str):
                    lastlist += entry
                else:
                    lastlist += entry.formatted(formatType, fence=False)
            print(lastlist)
            return lastlist, print('returning ' + str(lastlist))
        else:
            return self.getFormattedList(formatType, newList)

    def formattedNew(self, formatType, fence=False, subFence=False, operatorOrOperators=None, implicitFirstOperator=False,
                  wrapPositions=None, justification=None, orientation=None, **kwargs):
        from .expr_range import ExprRange

        outStr = ''
        if len(self) == 0 and fence:
            # for an empty list, show the parenthesis to show something.
            return '()'

        if wrapPositions is None:
            # Convert from a convention where position 'n' is after the nth comma to one in which the position '2n' is
            # after the nth operator (which also allow for position before operators).
            wrapPositions = [2 * pos for pos in self.wrapPositions()]
        if justification is None:
            justification = self.getStyle('justification', 'center')
        if orientation is None:
            orientation = self.getStyle('orientation', 'horizontal')

        do_wrapping = len(wrapPositions) > 0
        if fence: outStr = '(' if formatType == 'string' else r'\left('
        if do_wrapping and formatType == 'latex':
            outStr += r'\begin{array} {%s} ' % (justification[0] + justification[0] + justification[0] +
                                                justification[0] + justification[0] + justification[0])

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
                    sub_expr._use_explicit_parameterization(formatType))
                if isinstance(sub_expr.body, ExprTuple):
                    _fence = True
                else:
                    _fence = subFence
                #formatted_sub_expressions += sub_expr.getFormattedList(formatType)#sub_expr._formatted_checkpoints(
                    #formatType, fence=_fence, with_ellipses=True,
                    #operator=operatorOrOperators)
            #elif isinstance(sub_expr, ExprTuple):
                # always fence nested expression lists
             #   formatted_sub_expressions.append(sub_expr.getFormattedList(formatType))
            #else:
             #   formatted_sub_expressions.append(sub_expr.getFormattedList(formatType))
        list = []
        print('176 ' + str(formatted_sub_expressions))
        print('177 ' + str(self.getFormattedList(formatType, list)))
        formatted_sub_expressions+=self.getFormattedList(formatType, list)[0]
        print('179 ' + str(formatted_sub_expressions))
        # put the formatted operator between each of formattedSubExpressions
        for value in formatted_sub_expressions:
            if orientation[0] == 'h':
                pass
            else:
                pass
        for wrap_position in wrapPositions:
            if wrap_position % 2 == 1:
                # wrap after operand (before next operation)
                formatted_sub_expressions[(wrap_position - 1) // 2] += r' \\ '
            else:
                # wrap after operation (before next operand)
                formatted_sub_expressions[wrap_position // 2] = r' \\ ' + formatted_sub_expressions[wrap_position // 2]
        if operatorOrOperators is None:
            operatorOrOperators = ','
        elif isinstance(operatorOrOperators, Expression) and not isinstance(operatorOrOperators, ExprTuple):
            operatorOrOperators = operatorOrOperators.formatted(formatType)
        if isinstance(operatorOrOperators, str):
            # single operator
            formatted_operator = operatorOrOperators
            if operatorOrOperators == ',':
                # e.g.: a, b, c, d
                outStr += (formatted_operator + ' ').join(formatted_sub_expressions)
            else:
                # e.g.: a + b + c + d
                outStr += (' ' + formatted_operator + ' ').join(formatted_sub_expressions)
        else:
            # assume all different operators
            formatted_operators = []
            for operator in operatorOrOperators:
                if isinstance(operator, ExprRange):
                    # Handle an ExprRange entry; here the "operators"
                    # are really ExprRange "checkpoints" (first, last,
                    # as well as the ExprRange body in the middle if
                    # using an 'explicit' style for 'parameterization').
                    # For the 'ellipses', we will just use a
                    # placeholder.
                    be_explicit = using_explicit_parameterization.pop(0)
                    formatted_operators += operator._formatted_checkpoints(
                        formatType, fence=subFence, ellipses='',
                        use_explicit_parameterization=be_explicit)
                else:
                    formatted_operators.append(operator.formatted(formatType))
            if len(formatted_sub_expressions) == len(formatted_operators):
                # operator preceeds each operand
                if implicitFirstOperator:
                    outStr = formatted_sub_expressions[0]  # first operator is implicit
                else:
                    outStr = formatted_operators[0] + formatted_sub_expressions[0]  # no space after first operator
                outStr += ' '  # space before next operator
                outStr += ' '.join(
                    formatted_operator + ' ' + formatted_operand for formatted_operator, formatted_operand in
                    zip(formatted_operators[1:], formatted_sub_expressions[1:]))
            elif len(formatted_sub_expressions) == len(formatted_operators) + 1:
                # operator between each operand
                outStr = ' '.join(
                    formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in
                    zip(formatted_sub_expressions, formatted_operators))
                outStr += ' ' + formatted_sub_expressions[-1]
            elif len(formatted_sub_expressions) != len(formatted_operators):
                raise ValueError(
                    "May only perform ExprTuple formatting if the number of operators is equal to the number of operands (precedes each operand) or one less (between each operand); also, operator ranges must be in correpsondence with operand ranges.")

        if do_wrapping and formatType == 'latex':
            outStr += r' \end{array}'
        if fence: outStr += ')' if formatType == 'string' else r'\right)'
        print(outStr)
        return outStr

    def formatted(self, formatType, fence=False, subFence=False, operatorOrOperators=None, implicitFirstOperator=False,
                  wrapPositions=None, justification=None, orientation=None, **kwargs):
        from .expr_range import ExprRange

        outStr = ''
        if len(self) == 0 and fence:
            # for an empty list, show the parenthesis to show something.
            return '()'

        if wrapPositions is None:
            # Convert from a convention where position 'n' is after the nth comma to one in which the position '2n' is
            # after the nth operator (which also allow for position before operators).
            wrapPositions = [2 * pos for pos in self.wrapPositions()]
        if justification is None:
            justification = self.getStyle('justification', 'center')
        if orientation is None:
            orientation = self.getStyle('orientation', 'horizontal')

        do_wrapping = len(wrapPositions) > 0
        if fence: outStr = '(' if formatType == 'string' else r'\left('
        if do_wrapping and formatType == 'latex':
            outStr += r'\begin{array} {%s} ' % (justification[0] + justification[0] + justification[0] +
                                                justification[0] + justification[0] + justification[0])

        formatted_sub_expressions = []
        # Track whether or not ExprRange operands are using
        # "explicit" parameterization, because the operators must
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
                    sub_expr._use_explicit_parameterization(formatType))
                if isinstance(sub_expr.body, ExprTuple):
                    _fence = False
                    #if formatType == 'latex': sub_expr_body.entries
                    self.orientation(1,2)
                else:
                    _fence = False
                i = 0
                k = 0
                for expr in sub_expr._formatted_checkpoints(formatType,
                                                        fence=False, subFence=False,
                                                        ellipses=r'\vdots & & \vdots & \vdots & & \vdots',
                                                        operator=operatorOrOperators):
                    if i==0 & isinstance(sub_expr.first(), ExprTuple):
                        if isinstance(sub_expr.first().entries[0], ExprTuple):
                            expr = (sub_expr.first().entries[0].entries[0].formatted(formatType) + ' && ' +
                                    sub_expr.first().entries[0].entries[1].formatted(formatType))
                        elif isinstance(sub_expr.first().entries[0], ExprRange):
                            expr = (sub_expr.first().entries[0].first().formatted(formatType) + ' & ' +
                                    r'\cdots' + ' & ' +
                                    sub_expr.first().entries[0].last().formatted(formatType))
                        else:
                            expr = sub_expr.first().entries[0].formatted(formatType)
                        if isinstance(sub_expr.first().entries[1], ExprTuple):
                            expr += (' & ' + sub_expr.first().entries[1].entries[0].formatted(formatType) + ' && ' +
                                             sub_expr.first().entries[1].entries[1].formatted(formatType))
                        elif isinstance(sub_expr.first().entries[1], ExprRange):
                            expr += (' & ' + sub_expr.first().entries[1].first().formatted(formatType) +
                                     ' & ' + r'\cdots' +
                                     ' & ' + sub_expr.first().entries[1].last().formatted(formatType))
                        else:
                            expr += ' & ' + sub_expr.first().entries[1].formatted(formatType)
                    elif (expr == sub_expr.last().formatted(formatType, fence=False)) \
                            & isinstance(sub_expr.last(), ExprTuple):
                        if isinstance(sub_expr.last().entries[0], ExprTuple):
                            expr = (sub_expr.last().entries[0].entries[0].formatted(formatType) + ' && ' +
                                    sub_expr.last().entries[0].entries[1].formatted(formatType))
                        elif isinstance(sub_expr.last().entries[0], ExprRange):
                            expr = (sub_expr.last().entries[0].first().formatted(formatType) + ' & ' +
                                    r'\cdots' + ' & ' + sub_expr.last().entries[0].last().formatted(formatType))
                        else:
                            expr = sub_expr.last().entries[0].formatted(formatType)
                        if isinstance(sub_expr.last().entries[1], ExprTuple):
                            expr += (' & ' + sub_expr.last().entries[1].entries[0].formatted(formatType) + ' && ' +
                                             sub_expr.last().entries[1].entries[1].formatted(formatType))
                        elif isinstance(sub_expr.first().entries[0], ExprRange):
                            expr += (' & ' + sub_expr.last().entries[1].first().formatted(formatType) + ' & ' +
                                             r'\cdots' + ' & ' +
                                             sub_expr.last().entries[1].last().formatted(formatType))
                        else:
                            expr += ' & ' + sub_expr.last().entries[1].formatted(formatType)

                    formatted_sub_expressions.append(expr)
                    i += 1
                    print(formatted_sub_expressions)
            elif isinstance(sub_expr, ExprTuple):
                # always fence nested expression lists

                inc = 0
                for expr in sub_expr:
                    if inc == 0:
                        if isinstance(expr, ExprRange):
                            self.orientation(6)
                            formatted_sub_expressions.append(expr.first().formatted(formatType,
                                                                                    fence=False, subFence=False))
                            formatted_sub_expressions.append(r'& \cdots')
                            formatted_sub_expressions.append('& ' + expr.last().formatted(formatType,
                                                                                    fence=False, subFence=False))
                        else:
                            self.orientation(2)
                            formatted_sub_expressions.append(expr.formatted(formatType, fence=False, subFence=False))
                    #elif inc==1 or inc==3:
                     #   formatted_sub_expressions.append('&& ' + expr.formatted(formatType, fence=False, subFence=False))
                    else:
                        if isinstance(expr, ExprRange):
                            self.orientation(6)
                            formatted_sub_expressions.append('& ' + expr.first().formatted(formatType,
                                                                                    fence=False, subFence=False))
                            formatted_sub_expressions.append(r'& \cdots')
                            formatted_sub_expressions.append('& ' + expr.last().formatted(formatType,
                                                                                    fence=False, subFence=False))
                        else:
                            self.orientation(2)
                            formatted_sub_expressions.append('& ' + expr.formatted(formatType, fence=False, subFence=False))
                    inc+=1
            else:
                formatted_sub_expressions.append('& ' + sub_expr.formatted(formatType, fence=False, subFence=False))

        # put the formatted operator between each of formattedSubExpressions
        for wrap_position in wrapPositions:
            if wrap_position % 2 == 1:
                # wrap after operand (before next operation)
                formatted_sub_expressions[(wrap_position - 1) // 2] += r' \\ '
            else:
                # wrap after operation (before next operand)
                formatted_sub_expressions[wrap_position // 2] = r' \\ ' + formatted_sub_expressions[wrap_position // 2]
        if operatorOrOperators is None:
            operatorOrOperators = ','
        elif isinstance(operatorOrOperators, Expression) and not isinstance(operatorOrOperators, ExprTuple):
            operatorOrOperators = operatorOrOperators.formatted(formatType, fence=False)
        if isinstance(operatorOrOperators, str):
            # single operator
            formatted_operator = operatorOrOperators
            if operatorOrOperators == ',':
                # e.g.: a, b, c, d
                outStr += (' ').join(formatted_sub_expressions) #('&' + formatted_operator + ' ').join('&' + formatted_sub_expressions)
            else:
                # e.g.: a + b + c + d
                outStr += (' ').join(formatted_sub_expressions)
        else:
            # assume all different operators
            formatted_operators = []
            for operator in operatorOrOperators:
                if isinstance(operator, ExprRange):
                    # Handle an ExprRange entry; here the "operators"
                    # are really ExprRange "checkpoints" (first, last,
                    # as well as the ExprRange body in the middle if
                    # using an 'explicit' style for 'parameterization').
                    # For the 'ellipses', we will just use a
                    # placeholder.
                    be_explicit = using_explicit_parameterization.pop(0)
                    formatted_operators += operator._formatted_checkpoints(
                        formatType, fence=False, subFence=False, ellipses='',
                        use_explicit_parameterization=be_explicit)
                else:
                    formatted_operators.append(operator.formatted(formatType, fence=False, subFence=False))
            if len(formatted_sub_expressions) == len(formatted_operators):
                # operator preceeds each operand
                if implicitFirstOperator:
                    outStr = formatted_sub_expressions[0]  # first operator is implicit
                else:
                    outStr = formatted_operators[0] + formatted_sub_expressions[0]  # no space after first operator
                outStr += ' '  # space before next operator
                outStr += ' '.join(
                    formatted_operator + ' ' + formatted_operand for formatted_operator, formatted_operand in
                    zip(formatted_operators[1:], formatted_sub_expressions[1:]))
            elif len(formatted_sub_expressions) == len(formatted_operators) + 1:
                # operator between each operand
                outStr = ' '.join(
                    formatted_operand + ' ' + formatted_operator for formatted_operand, formatted_operator in
                    zip(formatted_sub_expressions, formatted_operators))
                outStr += ' ' + formatted_sub_expressions[-1]
            elif len(formatted_sub_expressions) != len(formatted_operators):
                raise ValueError(
                    "May only perform ExprTuple formatting if the number of operators is equal to the number of operands (precedes each operand) or one less (between each operand); also, operator ranges must be in correpsondence with operand ranges.")

        if do_wrapping and formatType == 'latex':
            outStr += r' \end{array}'
        if fence: outStr += ')' if formatType == 'string' else r'\right)'
        print(outStr)
        return outStr



