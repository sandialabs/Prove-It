from label import Label
from var import Variable
from proveit.core.expression.expr import MakeNotImplemented

class Literal(Label):
    """
    A Literal expresses contextual meaning.  Such Labels are not interchangeable.
    The Literal must be associated with a 'context' and should be the name of a package.
    Through Axiom elimination, a Literal may be converted to the var with the same
    label.
    """
    def __init__(self, context, stringFormat, latexFormat=None):
        '''
        Create a Lateral.  If latexFormat is not supplied, the stringFormat is used for both.
        '''
        try:
            self.context = str(context)
        except:
            raise TypeError("'context' must be a string or package")
        Label.__init__(self, stringFormat, latexFormat, 'Literal', [str(context)])
        '''
        if self.context is None or self.context[:7] != 'proveit':
            raise Exception('Literal package must be contained within proveit.  This may result from a relative import.\nUse absolute imports with proveit Literals.')
        '''
    
    def asVariable(self):
        '''
        Return the var with the same label as this Literal.
        '''
        return Variable(self.stringFormate, self.latexFormat)
    
    @classmethod
    def _make(literalClass, coreInfo, subExpressions):
        if len(subExpressions) > 0:
            raise ValueError('Not expecting any subExpressions of Literal')
        if len(coreInfo) != 4:
            raise ValueError("Expecting " + literalClass.__name__ + " coreInfo to contain 4 items: '" + literalClass.__name + "', stringFormat, latexFormat, and the context")
        if coreInfo[0] != 'Literal':
            raise ValueError("Expecting coreInfo[0] to be 'Literal'")
        return literalClass(coreInfo[2], coreInfo[0], coreInfo[1])
