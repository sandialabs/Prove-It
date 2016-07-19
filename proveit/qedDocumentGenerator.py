import xml.etree.ElementTree as ET
from proveit import expression
from proveit.expression import *
import os

class DocumentGenerator:
    """
    Generate rst documents for wiki-QED web pages that show 
    proof derivations and expression trees.
    """
    def __init__(self):
#        self.basePath = os.path.join(os.path.dirname(expression.__file__), 'qed-doc')
        self.basePath = os.path.join(os.path.dirname(expression.__file__), '../qed-doc')
    
    def expressionCategoryClass(self, expr):
        '''
        Return the inherited class of the expression that is one of the basic expression categories.
        '''
        if isinstance(expr, ExpressionList):
            return ExpressionList
        elif isinstance(expr, Operation):
            return Operation
        elif isinstance(expr, Lambda):
            return Lambda
        elif isinstance(expr, MultiVariable):
            return MultiVariable
        elif isinstance(expr, Variable):
            return Variable
        elif isinstance(expr, Literal):
            return Literal
    
    def expressionTypeAndCategory(self, expr):
        '''
        Returns the Sphinx references to the type of the given expression and its catagorical inherited type.
        '''
        if expr.__class__.__module__ == expression.__name__:
            return ':py:class:`' + str(self.expressionCategoryClass(expr)) + '`' # one of the standard expression types
        else:
            return ':py:class:`' + str(expr.__class__) + r'` \:\: :py:class:`' + str(self.expressionCategoryClass(expr))  + '`'
    
    def genExpressionTree(self, expr, out, indentation = ''):
        '''
        Generate the restructured test for the expression tree of the given expression,
        writing it out to the 'out' stream.
        '''
        if indentation == '':
            # form the title
            titleStr = ':math:`' + expr.formatted(LATEX) + '`'
            print >>out, titleStr
            print >>out, '='*len(titleStr) + '\n'
            print >>out, 'Expression Tree'
            print >>out, '---------------\n'
        if isinstance(expr, Literal):
            out.write(str(expr.context) + "." + expr.name)
        else:
            out.write(':math:`' + expr.formatted(LATEX) + '`')
        out.write(' ; ' + self.expressionTypeAndCategory(expr))
        subExpressionsAndRoles = None
        if isinstance(expr, ExpressionList):
            subExpressionsAndRoles = [(subExpr, None) for subExpr in expr.expressions]
        elif isinstance(expr, Operation):
            subExpressionsAndRoles = ((expr.operator, 'operator'), (expr.etcExpr, 'etcExpr'))
        elif isinstance(expr, Lambda):
            subExpressionsAndRoles = ((expr.argument, 'argument'), (expr.expression, 'expression'), (expr.domainCondition, 'condition'))
        if not subExpressionsAndRoles is None:
            indentation += '\t'
            for subExpr, role in subExpressionsAndRoles:
                if isinstance(subExpr, ExpressionList) and len(subExpr) == 0:
                    continue # skip an empyt list sub-expression
                out.write('\n' + indentation + '* ')
                if not role is None:
                    out.write(role + r"\: ")
                self.genExpressionTree(subExpr, out, indentation)

    def genDerivationTree(self, context, prover, out, indentation=''):
        '''
        Generate the restructured test for the derivation tree of the given prover,
        writing it out to the 'out' stream.
        '''
        stmt = prover.stmtToProve    
        isRoot = (indentation == '')        
        if not isRoot:
            out.write(prover.proverType +' ')
        out.write(self.exprTreeRef(context, stmt))
        if not prover.provingAssumptions is None:
            if len(prover.provingAssumptions) == 1 and prover.stmtToProve in prover.provingAssumptions:
                out.write(' by assumption')
            elif len(prover.provingAssumptions) > 0:
                out.write(' assuming')
                out.write('(' + ", ".join([self.exprTreeRef(context, assumption) for assumption in prover.provingAssumptions]) + ')')
        if not prover.subMap is None and len(prover.subMap) > 0:
            def subMapToRST(var, subExpr):
                return self.exprTreeRef(context, var) + ' : ' +  self.exprTreeRef(context, subExpr)
            out.write(' via {' + ', '.join(subMapToRST(var, subExpr) for var, subExpr in prover.subMap) +'}')
        out.write('\n')
        indentation += '\t'
        if not isRoot and stmt.hasName():
            linkContext, stmtName = stmt.getContextAndName()
            out.write(indentation + '* ')
            if stmt.isAxiom(): 
                print >>out, 'by axiom: ' + self.axiomRef(linkContext, stmtName)
            elif stmt.isNamedTheorem(): 
                print >>out, 'by theorem: ' + self.theoremRef(linkContext, stmtName)
        elif not isRoot and stmt.isProvenTheorem() and not prover.provers is None and not all(subProver.provers is None for subProver in prover.provers):
            print >>out, indentation + '* by ' + self.unnamedTheoremRef(context, prover)
        elif not prover.provers is None:
            for i, subProver in enumerate(prover.provers):
                out.write(indentation + '* ')
                out.write("by " if i == 0 else "and ")
                self.genDerivationTree(context, subProver, out, indentation)
    
    def hashRST(self, context, dirName, expr, genTextFn):
        '''
        Make a unique filename for the given expression based upon the expression's hash code.
        Place the file under dirName in the base path of the context's package.
        Call genTextFn to write the restructured text to this file if it doesn't already exist.
        '''
        # Go to the package level that the context is contained in.
        packageDirList = [self.basePath] + context.name.split('.')
        packageDirList.pop(-1)
        packageDirList.append(dirName)
        if not os.path.isdir(os.path.join(*packageDirList)):
            os.mkdir(os.path.join(*packageDirList))
        exprRep = repr(expr)
        exprHash = hex(abs(hash(expr)))
        # match the hash, with an extra index after it, with a text file that has the expressions
        # representation string.  this is to deal with hash conflicts
        pathFn = lambda i : os.path.join(*(packageDirList + [exprHash + '_' + str(i)]))
        i = 0
        while os.path.isfile(pathFn(i) + '.txt'):
            repInTxt = open(pathFn(i) + '.txt', 'r').read()
            if repInTxt == exprRep: break
            i += 1
        path = pathFn(i)
        if not os.path.isfile(path + '.txt'):
            open(path + '.txt', 'w').write(exprRep)
            # build the expression page and write it out
            out = open(path + '.rst', 'w')
            genTextFn(out)
        # return the relative path
        return os.path.relpath(path, self.basePath)
        
    def exprTreeRef(self, context, stmtOrExpr):
        '''
        Generate and write an expression tree restructured text file (if it doesn't already exist), 
        and return the reference.
        '''
        expr = stmtOrExpr.getExpression() if isinstance(stmtOrExpr, KnownTruth) else stmtOrExpr
        return ':doc:`/' + self.hashRST(context, 'expressions_', expr, lambda out : self.genExpressionTree(expr, out)) + '`'

    def unnamedTheoremRef(self, context, prover):
        '''
        Generate and write a derivation tree restructured text file (if it doesn't already exist)
        for an unnamed theorem, and return the reference.
        '''
        stmt = prover.stmtToProve
        expr = stmt.getExpression()        
        def genUnnamedTheoremPageFn(out):
            # form the title
            titleStr = ':math:`' + expr.formatted(LATEX) + '`'
            print >>out, titleStr
            print >>out, '='*len(titleStr) + '\n'
            print >>out, 'Proof of unnamed theorem'
            print >>out, '------------------------\n'
            self.genDerivationTree(context, prover, out)
        return ':doc:`/' + self.hashRST(context, 'unnamed_theorems_', expr, genUnnamedTheoremPageFn) + '`'

    def theoremRef(self, context, theoremName, showContext=True):
        '''
        Reference a theorem document.
        '''
        if showContext:
            linkDisplay = str(context)  + '.' + theoremName
        else:
            linkDisplay = theoremName
        return ':doc:`' + linkDisplay + ' </' + str(context).replace('.', '/') + '/' + theoremName + '>`'

    def axiomRef(self, context, axiomName, showContext=True):
        '''
        Make a reference to an axiom.
        '''
        return ':ref:`' + str(context) + '.' + axiomName + ' <' + str(context) + '.' + axiomName + '>`'

    def theoremModule(self, context, theoremName):
        '''
        Return the name of the theorem module for the given theorem following a specific convention
        of putting it in a package derived from the context's name (with underscored before and after)
        '''
        lst = context.name.split('.')
        lst[-1] = lst[-1] + '_'
        lst.append(theoremName)
        return 'proveit.' + '.'.join(lst)
    
    def makeTheoremRST(self, context, theoremName, theoremExpr):
        '''
        Make the restructured text file for the given theorem (in the given context with the given name).
        '''
        thmPath = os.path.join(*([self.basePath] + context.name.split('.') + [theoremName + '.rst']))
        print "thmPath", thmPath
        out = open(thmPath, 'w')
        titleStr = 'Proof of :py:mod:`' + self.theoremModule(context, theoremName) + '` in :py:mod:`proveit.' + str(context) + '`'
        print >>out, titleStr
        print >>out, '='*len(titleStr) + '\n'
        self.genDerivationTree(context, theoremExpr.statement.getProver(), out)
        out.close()

    def makeContextRST(self, context):
        """
        Make the restructured text file for the given context.
        """
        pathLst = context.name.split('.')
        pathLst[-1] = pathLst[-1] + '.rst'
        filePath = os.path.join(*([self.basePath] + pathLst))
        out = open(filePath, 'w')
        titleStr = 'Context: ' + str(context)
        print >>out, titleStr
        print >>out, '='*len(titleStr) + '\n'
        axiomDict = context.getAxiomDictionary() 
        thmDict = context.getTheoremDictionary() 
        print >>out, 'Axioms'
        print >>out, '------'
        for axiomName in context.creationOrderAxiomNames():
            print >>out, '.. _' + str(context) + axiomName + ':'
            print >>out, axiomName
            print >>out, '\t* ' + self.exprTreeRef(context, axiomDict[axiomName])
        print >>out, 'Named Theorems'
        print >>out, '--------------'
        for theoremName in context.creationOrderTheoremNames():
            print >>out, self.theoremRef(context, theoremName, showContext=False)
            print >>out, '\t* ' + self.exprTreeRef(context, thmDict[theoremName])
        out.close()
