from label import Label
from proveit.core.expression.expr import MakeNotImplemented

class MultiVariable(Label):
    '''
    A MultiVariable is a single label that may be expanded to zero or more Variable's.
    It uses dummy axes symbols (Labels) to indicate that it may be expanded in one
    or more dimensions.
    '''
    defaultAxesLabels = [Label('*', r'\Box'), Label('@', r'\triangle'), Label('#', r'\Diamond')]
    
    def __init__(self, stringFormat, latexFormat=None, numDimensions = None, axesLabels = None):
        '''
        Create a MultiVariable.  If latexFormat is not supplied, the stringFormat is used for both.
        By default, it has a single axis with the MultiVariable.defaultAxesLabels[0] label.
        If numAxes is specified and axesLabels is not, it uses 
        MultiVariable.defaultAxesLabels[:numAxes] as the axes labels.  If axesLabels
        is provided, it is not necessary to provide numAxes.
        '''
        if numDimensions is None:
            numDimensions = 1 if axesLabels is None else len(axesLabels)
        if numDimensions < 1:
            raise ValueError("a MultiVariable must be in one or more dimensions")
        if axesLabels is None:
            if numDimensions > len(MultiVariable.defaultAxesLabels):
                raise ValueError("not enough defaultAxesLabels for the specified 'numDimensions'")
        elif numDimensions != len(axesLabels):
            raise ValueError("number of 'axesLabels' must match 'numDimensions'")
        self.numIndices = numDimensions
        if axesLabels is None: axesLabels = MultiVariable.defaultAxesLabels[:numDimensions]
        self.axesLabels = axesLabels
        extraCoreInfo = []
        for axisLabel in axesLabels:
            extraCoreInfo += axisLabel._labelInfo()
        Label.__init__(self, stringFormat, latexFormat, 'MultiVariable', extraCoreInfo)

    @classmethod
    def make(subClass, coreInfo, subExpressions):
        if subClass != MultiVariable: 
            raise MakeNotImplemented(subClass)
        if len(subExpressions) > 0:
            raise ValueError('Not expecting any subExpressions of Variable')
        if len(coreInfo) >= 5:
            raise ValueError("Expecting MultiVariable coreInfo to contain at least 5 items: 'MultiVariable', stringFormat, latexFormat, axis label stringFormat, axis label latexFormat")
        if len(coreInfo) % 2 == 0:
            raise ValueError("Expecting MultiVariable coreInfo to contain an odd number of items: 'MultiVariable' followed by stringFormat, latexFormat pairs for the axes' labels")
        if coreInfo[0] != "MultiVariable":
            raise ValueError("Expecting coreInfo[0] to be 'MultiVariable'")
        stringFormat, latexFormat = coreInfo[1:3]
        axesLabels = []
        for axis in range((len(coreInfo) - 3)/2):
            axisStringFormat, indexLatexFormat = coreInfo[3+2*axis:3+2*(axis+1)]
            axesLabels.append(Label(axisStringFormat, indexLatexFormat))
        return MultiVariable(stringFormat, latexFormat, axesLabels = axesLabels)

    def string(self, **kwargs):
        indicesStr = ' '.join(self.axesLabels[k].string() for k in range(self.numIndices))
        return Label.string(self) + '_{' + indicesStr + '}'
    
    def latex(self, **kwargs):
        indicesStr = ' '.join(self.axesLabels[k].latex() for k in range(self.numIndices))
        return Label.latex(self) + '_{' + indicesStr + '}'
        
    def substituted(self, exprMap, relabelMap = None, reservedVars = None):
        return self.variable.substituted(exprMap, relabelMap, reservedVars)

    def usedVars(self):
        return self.variable.usedVars()

    def freeVars(self):
        return self.variable.freeVars()

    def freeMultiVars(self):
        return {self}
