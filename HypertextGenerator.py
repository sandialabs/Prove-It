import xml.etree.ElementTree as ET
import statement
from statement import *
import os

class HypertextGenerator:
    def __init__(self):
        pass
    
    def expressionCategory(self, expr):
        if isinstance(expr, ExpressionList):
            return 'ExpressionList'
        elif isinstance(expr, Operation):
            return 'Operation'
        elif isinstance(expr, Lambda):
            return 'Lambda'
        elif isinstance(expr, MultiVariable):
            return 'MultiVariable'
        elif isinstance(expr, Variable):
            return 'Variable'
        elif isinstance(expr, Literal):
            return 'Literal'
    
    def expressionTypeAndCategory(self, expr):
        if expr.__class__.__module__ == statement.__name__:
            return self.expressionCategory(expr) # one of the standard expression types
        else:
            return str(expr.__class__) + ' :: ' + self.expressionCategory(expr) 
    
    def genExpressionTreeHTML(self, path, expr):
        outStr = ''
        if isinstance(expr, Literal):
            outStr += str(expr.context) + "." + expr.name
        else:
            outStr += '<math>' + expr.formatted(MATHML) + '</math>'
        outStr += ' <span class="exprType">(' + self.expressionTypeAndCategory(expr) + ')</span>'
        subExpressionsAndRoles = None
        if isinstance(expr, ExpressionList):
            subExpressionsAndRoles = [(subExpr, None) for subExpr in expr.expressions]
        elif isinstance(expr, Operation):
            subExpressionsAndRoles = ((expr.operator, 'operator'), (expr.operand, 'operand'))
        elif isinstance(expr, Lambda):
            subExpressionsAndRoles = ((expr.argument, 'argument'), (expr.expression, 'expression'), (expr.domainCondition, 'condition'))
        if not subExpressionsAndRoles is None:
            outStr += '<ul class="subExpr">'
            for subExpr, role in subExpressionsAndRoles:
                if isinstance(subExpr, ExpressionList) and len(subExpr) == 0:
                    continue # skip an empyt list sub-expression
                outStr += '<li class="exprItem">'
                if not role is None:
                    outStr += '<span class="exprRole">' + role + "</span>: "
                outStr += self.genExpressionTreeHTML(path, subExpr)
                outStr += '</li>'
            outStr += '</ul>'            
        return outStr
    
    def exprHashFile(self, fromPath, context, dirName, expr, genPageFn):
        '''
        Make a unique filename for the given expression based upon the expression's hash code.
        Place the file under dirName in the base path of the context's package.
        '''
        # Go to the package level that the context is contained in.
        packageDirList = [self.basePath()] + context.name.split('.')
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
        print "PATH: " + path
        if not os.path.isfile(path + '.txt'):
            open(path + '.txt', 'w').write(exprRep)
            # build the expression page and write it out
            open(path + '.html', 'w').write(genPageFn(path))
        # return the relative path
        return os.path.relpath(path + '.html', os.path.split(fromPath)[0])
        

    def exprPage(self, fromPath, context, stmtOrExpr):
        expr = stmtOrExpr.getExpression() if isinstance(stmtOrExpr, Statement) else stmtOrExpr
        return self.exprHashFile(fromPath, context, '__expressions__', expr, lambda path : '<html><body><h1>Expression Tree</h1>' + self.genExpressionTreeHTML(path, expr) + '</html></body>')
    
    def unnamedTheoremPage(self, fromPath, context, prover):
        stmt = prover.stmtToProve
        expr = stmt.getExpression()
        print "UNNAMED THEOREM"
        def genUnnamedTheoremPageFn(path):
            stylePath = self.relStylePath(path)
            htmlStr = '<html><head><link rel="stylesheet" type="text/css" href="' + stylePath + '"></head><body>' 
            htmlStr += '<h1>Proof of unnamed theorem</h1>'
            htmlStr += self.genDerivationTreeHTML(path, context, prover)
            htmlStr += '</body></html>'
            return htmlStr
        return self.exprHashFile(fromPath, context, '__unnamed_theorems__', expr, genUnnamedTheoremPageFn)
        
    def linkedExpr(self, fromPath, context, stmtOrExpr):
        expr = stmtOrExpr.getExpression() if isinstance(stmtOrExpr, Statement) else stmtOrExpr
        return '<a class="exprLink" href="' + self.exprPage(fromPath, context, expr) + '"><math>' + expr.formatted(MATHML) + '</math></a>'

    def linkedUnnamedTheorem(self, fromPath, context, prover):            
        expr = prover.stmtToProve.getExpression()
        return '<a href="' + self.unnamedTheoremPage(fromPath, context, prover) + '">unnamed theorem</a>'
        
    def genDerivationTreeHTML(self, path, context, prover, onlyEssentialSteps=True, isRoot=True):
        stmt = prover.stmtToProve            
        outStr = ''
        if not isRoot:
            outStr += '<span class="proverType">' + prover.proverType + '</span> '
        outStr += self.linkedExpr(path, context, stmt)
        if not prover.provingAssumptions is None:
            if len(prover.provingAssumptions) == 1 and prover.stmtToProve in prover.provingAssumptions:
                outStr += ' <span class="assuming">by assumption</span>'
            elif len(prover.provingAssumptions) > 0:
                outStr += ' <span class="assuming">assuming</span> '
                outStr += '(' + ", ".join([self.linkedExpr(path, context, assumption) for assumption in prover.provingAssumptions]) + ')'
        if not prover.subMap is None and len(prover.subMap) > 0:
            def subMapToHTML(var, subExpr):
                return self.linkedExpr(path, context, var) + ' : ' +  self.linkedExpr(path, context, subExpr)
            outStr += ' via {' + ', '.join(subMapToHTML(var, subExpr) for var, subExpr in prover.subMap) +'}'
        if not isRoot and stmt.hasName():
            linkContext, stmtName = stmt.getContextAndName()
            outStr += '<ul><li class="namedStmt">' 
            if stmt.isAxiom(): outStr += 'by axiom: <b>' + str(context) + '.' + stmtName + '</b>'
            elif stmt.isNamedTheorem(): 
                outStr += 'by theorem: '
                outStr += self.linkedTheorem(path, linkContext, stmtName)
            outStr += '</li></ul>'
        elif not isRoot and stmt.isProvenTheorem() and not prover.provers is None and not all(subProver.provers is None for subProver in prover.provers):
            outStr += '<ul><li class="unnamedTheorem">by ' + self.linkedUnnamedTheorem(path, context, prover) + '</li></ul>'
        elif not prover.provers is None:            
            outStr += '<ul class="subDerivation">'
            for i, subProver in enumerate(prover.provers):
                outStr += '<li class "derivationItem">'
                outStr += "by " if i == 0 else "and "
                outStr += self.genDerivationTreeHTML(path, context, subProver, onlyEssentialSteps, isRoot=False)
                outStr += '</li>'
            outStr += '</ul>'
        return outStr    
    
    def basePath(self):
        return os.path.dirname(statement.__file__)
    
    def theoremPath(self, context, theoremName):
        pathList = context.name.split('.')
        pathList[-1] = '_' + pathList[-1] + '_'
        pathList.append(theoremName + '.html')
        return os.path.join(self.basePath(), *pathList)
    
    def relStylePath(self, fromPath):
        return os.path.relpath(os.path.join(self.basePath(), 'style.css'), os.path.split(fromPath)[0]) 
    
    def linkedTheorem(self, fromPath, context, theoremName):
        thmPath = self.theoremPath(context, theoremName)
        relPath = os.path.relpath(thmPath, os.path.split(fromPath)[0])
        return '<a href="' + relPath + '">' + str(context) + "." + theoremName + '</a>'
    
    def makeTheoremPage(self, context, theoremName, theoremExpr):
        thmPath = self.theoremPath(context, theoremName)
        outFile = open(thmPath, 'w')
        stylePath = self.relStylePath(thmPath)
        htmlStr = '<html><head><link rel="stylesheet" type="text/css" href="' + stylePath + '"></head><body>' 
        htmlStr += '<h1>Proof of <a href=' + theoremName + '.py>' + theoremName + '</a> in ' + str(context) + '</h1>'
        htmlStr += self.genDerivationTreeHTML(thmPath, context, theoremExpr.statement.getProver()) + '</body></html>'
        outFile.write(htmlStr)
        outFile.close()
        
    def makeContextPage(self, context):
        # The context page has a path as if it were a theorem called '_context_'.
        # Actual named theorems should not begin/end in '_'.
        path = self.theoremPath(context, '_context_') 
        outFile = open(path, 'w')
        stylePath = self.relStylePath(path)
        htmlStr = '<html><head><link rel="stylesheet" type="text/css" href="' + stylePath + '"></head><body><h1>Context: ' + str(context) + '</h1>'
        axiomDict = context.getAxiomDictionary() 
        thmDict = context.getTheoremDictionary() 
        htmlStr += '<h2>Axioms:</h2><dl>'
        for axiomName in context.creationOrderAxiomNames():
            htmlStr += '<dt>' + axiomName + '</dt>'
            htmlStr += '<dd>' + self.linkedExpr(path, context, axiomDict[axiomName]) + '</dd>'
        htmlStr += '</dl><h2>Named theorems:</h2><dl>'
        for theoremName in context.creationOrderTheoremNames():
            htmlStr += '<dt>' + self.linkedTheorem(path, context, theoremName) + '</dt>'
            htmlStr += '<dd>' + self.linkedExpr(path, context, thmDict[theoremName]) + '</dd>'
        htmlStr += '</dl></body></html>'
        outFile.write(htmlStr)
        outFile.close()
