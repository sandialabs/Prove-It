from proveit.decorators import equality_prover
from proveit._core_.expression.label.literal import Literal
from proveit._core_.expression.operation import Operation
from proveit._core_.defaults import defaults, USE_DEFAULTS
from proveit._core_.proof import UnsatisfiedPrerequisites


class ConditionalSet(Operation):
    # operator of the ConditionalSet operation
    _operator_ = Literal(string_format='CondSet',
                         latex_format=r'\textrm{CondSet}', theory=__file__)

    def __init__(self, *conditionals, styles=None):
        Operation.__init__(self, ConditionalSet._operator_, conditionals,
                           styles=styles)
        self.conditionals = self.operands

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, must_evaluate=False, **defaults_config):
        '''
        Reduce a conditional set with one and only one TRUE condition
        where the other conditions are FALSE if applicable.
        '''
        try:
            return self.single_case_via_elimination()
        except UnsatisfiedPrerequisites as _e:
            raise NotImplementedError('shallow_simplification is only implemented '
                                      'if all conditions are known to be TRUE or FALSE', _e)
    # single_case_via_elimination

    @equality_prover('reduced_to_true_case', 'reduce_to_true_case')
    def single_case_via_elimination(self, **defaults_config):
        '''
        Automatically reduce a conditional set with one and only one TRUE condition
        where the other conditions are FALSE.
        '''
        from proveit import a, b, c, m, n, ExprTuple
        from proveit.logic import FALSE, TRUE
        from proveit.core_expr_types.conditionals import true_case_reduction
        from proveit._core_.expression.conditional import Conditional

        _b = None
        index = None
        for i, item in enumerate(self.conditionals):
            if isinstance(item, Conditional):
                if item.condition == TRUE:
                    if _b is not None:
                        raise UnsatisfiedPrerequisites(
                            "All conditions must be FALSE except one, both %s and %s are not FALSE: %s" % (
                            _b, item.string(), self))
                    _b = item.value
                    index = i
                elif item.condition != FALSE:
                    raise UnsatisfiedPrerequisites(
                            "All conditions must be FALSE except one, %s is not FALSE: %s" % (item.condition.string(),
                                                                                              self))
            else:
                if _b is not None:
                    raise UnsatisfiedPrerequisites(
                        "All conditions must be FALSE except one, both %s and %s are not FALSE: %s" % (_b,
                                                                                                       item.string(),
                                                                                                       self))
                else:
                    _b = item
                    index = i
        _a = [entry.value if isinstance(entry, Conditional) else entry for entry in self.conditionals[:index]]
        _c = [entry.value if isinstance(entry, Conditional) else entry for entry in self.conditionals[index+1:]]
        _m = self.conditionals[:index].num_elements()
        _n = self.conditionals[index+1:].num_elements()
        return true_case_reduction.instantiate({m: _m, n: _n, a: _a, b: _b, c: _c})

    def string(self, **kwargs):
        return self.formatted('string', **kwargs)

    def latex(self, **kwargs):
        return self.formatted('latex', **kwargs)

    def formatted(self, format_type, fence=None, **kwargs):
        #print(solo)
        if format_type == 'string':
            inner_str = '; '.join(conditional.formatted('string', fence=False, **kwargs)
                                  for conditional in self.conditionals)
            return '{' + inner_str + '.'
        else:
            from proveit import ExprRange
            formatted_conditionals = []
            for conditional in self.conditionals:
                if isinstance(conditional, ExprRange):
                    formatted_conditionals.append(conditional.first().formatted(format_type, fence=False, **kwargs))
                    formatted_conditionals.append(r' \vdots')
                    formatted_conditionals.append(conditional.last().formatted(format_type, fence=False, **kwargs))
                else:
                    formatted_conditionals.append(conditional.formatted('latex', fence=False, **kwargs))
            inner_str = r' \\ '.join(formatted_conditionals)
            inner_str = r'\begin{array}{ccc}' + inner_str + r'\end{array}'
            inner_str = r'\left\{' + inner_str + r'\right..'
            return inner_str
