'''
Created on Sep 30, 2013

@author: wwitzel
'''

import sys
import collections

from PySide import QtGui, QtCore, QtSvg
from proveItCore import *
from xml import sax
from svgmath.tools.saxtools import XMLGenerator, ContentFilter
from svgmath.mathhandler import MathHandler, MathNS
import StringIO
from bisect import bisect_left

renderedExpressions = dict()    
def renderedExpr(expr):
    if not expr in renderedExpressions:
        output = StringIO.StringIO() 
        config = open("svgmath.xml", "r")    
        # Create the converter as a content handler. 
        saxoutput = XMLGenerator(output, 'utf-8')
        handler = MathHandler(saxoutput, config)
        # Parse input file with a namespace-aware SAX parser
        parser = sax.make_parser()
        parser.setFeature(sax.handler.feature_namespaces, 1)
        parser.setContentHandler(handler)
        mathmlStr = "<math display='block'>"
        if isinstance(expr, tuple):
            expressions = expr
            mathmlStr += '<mo>,</mo>'.join([expr.formatted(MATHML) for expr in expressions])
            expr = expressions
        else:
            mathmlStr += expr.formatted(MATHML)
        mathmlStr += "</math>"
        parser.parse(StringIO.StringIO(mathmlStr))
        renderedExpressions[expr] = output.getvalue()
    return QtCore.QByteArray(renderedExpressions[expr])

class DerivationStep:
    def __init__(self, provers, onlyEssentialSteps = True, proofNumber = None, isRoot = True, autoAliasChild = True):
        self.parent = None
        self.provers = tuple(provers)
        if isRoot:
            self.proofNumber = provers[0].stmtToProve.proofNumber
        else:
            self.proofNumber = proofNumber
        self.onlyEssentialSteps = onlyEssentialSteps
        self.howProven = None
        self.children = None
        self.assumptions = None        
        self.stepType = None
        if len(self.provers) > 1:
            for prover in provers:
                self._makeChild([prover])
            self.stepType = 'composite'
            if self.wasProven():
                self.howProven = 'composition'
        else:
            prover = self.provers[0]
            if autoAliasChild:
                self.stepType = prover.proverType
                if prover.stmtToProve.wasProven() and prover.stmtToProve.getRegisteredVar() != None:
                    # this is either the root alias with the child as the aliased statement
                    # or a theorem statement with the child as the alias.
                    self._makeChild([prover], autoAliasChild=False) # autoAliasChild as False prevents infinite recursion
                    if isRoot:
                        # A root alias
                        self.stepType = 'alias'
                        self.howProven = 'derivation'
                        self.children[0].stepType = 'root'
                    else:
                        # an aliased theorem -- make the child be the alias
                        self.children[0].stepType = 'alias'
                        self.children[0].howProven = self.howProven = 'theorem' # may be overridden as 'axiom'
                        self.children[0].children = [] # no children for the theorem alias
            if prover.stmtToProve.isAxiom():
                self.howProven = 'axiom'
                if self.children == None:
                    self.children = []
                else:
                    self.children[0].howProven = 'axiom'
            elif prover.stmtToProve in prover.assumptions:
                self.howProven = 'assumption'
                self.children = []
    
    def isAliasLink(self):
        return self.stepType == 'alias' and len(self.children) == 0
    
    def isRoot(self):
        return self.parent == None

    def _makeDescendant(self, provers, autoAliasChild=True):
        return DerivationStep(provers, self.onlyEssentialSteps, self.proofNumber, False, autoAliasChild)
    
    def _makeChild(self, provers, autoAliasChild=True):
        child = self._makeDescendant(provers, autoAliasChild)
        if self.children == None:
            self.children = []
        self.children.append(child)
        child.parent = self
        if child.wasProven() and self.howProven == None:
            self.howProven = child.stepType
        return child
    
    def _setChildren(self, children):
        self.children = children
        for child in children:
            child.parent = self
            
    def wasProven(self):
        return all([prover.wasProven() for prover in self.provers])
    
    def getStatement(self):
        if len(self.provers) > 1:
            return [prover.stmtToProve for prover in self.provers]
        else:
            prover = self.provers[0]                
            if self.stepType == 'alias':
                return prover.stmtToProve.getRegisteredVar()
            else:
                return prover.stmtToProve
    
    def matchesStatements(self, stmts):
        return {prover.stmtToProve for prover in self.provers} == stmts
    
    def getAssumptionSet(self):
        if len(self.provers) > 1:
            assumptionSets = [child.getAssumptionSet() for child in self.children]
            return set().union(*assumptionSets)
        else:
            prover = self.provers[0]
            if self.wasProven():
                return prover.provingAssumptions # stmtToProve.provenAssumptions(prover.assumptions)
            else:
                return prover.assumptions
    
    def getAssumptions(self):
        """
        Get's the assumptions ordered in the same order as the parent with new
        additions at the end.
        """
        if self.assumptions != None:
            return self.assumptions
        assumptionSet = self.getAssumptionSet()
        parentAssumptions = self.parent.getAssumptions() if self.parent != None else []
        assumptions = [assumption for assumption in parentAssumptions if assumption in assumptionSet]
        remainingAssumptions = assumptionSet.difference(set(parentAssumptions))
        newAssumptions = [assumption for assumption in self.provers[0].newAssumptionsInOrder if assumption in remainingAssumptions]
        assumptions += newAssumptions
        remainingAssumptions = remainingAssumptions.difference(set(newAssumptions))
        assumptions += list(remainingAssumptions)
        self.assumptions = assumptions
        return assumptions
        
    def getData(self, name):
        if name == 'Statement':
            return self.getStatement()
        elif name == 'Assumptions':
            return [assumption for assumption in self.getAssumptions()]
        elif name == 'Step Type':
            return self.stepType
        elif name == 'How Proven':
            return self.howProven if self.howProven != None else 'N/A'
        elif name == 'Context':
            return self.provers[0].stmtToProve.getRegisteredContext()
        elif name == 'Proven':
            #return self.provers[0].stmtToProve.proofNumber
            return self.wasProven()

    def getDisplayData(self, name):
        data = self.getData(name)
        if isinstance(data, str):
            return data
        elif isinstance(data, collections.Iterable):
            if all([isinstance(datum, Statement) for datum in data]):
                return renderedExpr(tuple([datum.getExpression() for datum in data]))
            else:
                return ", ".join([str(x) for x in data])
        elif isinstance(data, Statement):
            return renderedExpr(data.getExpression())
        else:
            return str(data)

    def makeChildren(self):
        if self.children == None:
            if self.onlyEssentialSteps and len(self.provers) == 1 and self.provers[0].provers != None:
                for childProver in self.provers[0].provers:
                    self._makeChild([childProver])
                return
                #assert self._makeProofTree(), "Statement was proven but unable to make a proof tree -- shouldn't legitimately happen"
                #return
            prover = self.provers[0]
            childrenProvers = []
            prover.appendProvers(childrenProvers)
            self.children = []
            childProverGroups = set()
            for childProver in childrenProvers:
                if childProver.isCircular():
                    continue # skip circular reasoning
                corequisites = tuple(childProver.corequisites)
                #if self.onlyEssentialSteps and self.wasProven():
                #    if not childProver.stmtToProve in prover.stmtToProve.provingStatements(set(prover.assumptions)):
                #        continue # only go with what is known
                if len(corequisites) == 1: 
                    # only self as corequisite
                    self._makeChild([childProver])
                elif not corequisites in childProverGroups:
                    childProverGroups.add(corequisites)
                    self._makeChild(corequisites)
            if len(self.children) == 1 and self.children[0].stepType == 'composite':
                # If there is only one composite child, we can skip over it to its children
                self.children = self.children[0].children
                for child in self.children:
                    child.parent = self
                    
    def _makeProofTree(self):
        pvr2step = dict() # maps Statement.Prover to DerivationStep as the tree completes from the bottom up
        breadth1stQueue = list(self.provers)
        while len(breadth1stQueue) > 0:
            prover = breadth1stQueue.pop(0)
            #print prover.depth, prover.stmtToProve, [assumption.getExpression() for assumption in prover.assumptions], "proven?", prover.wasProven(), "Leaf?", self._proverIsLeaf(prover)
            if prover.isCircular(): continue
            if not prover.wasProven(): continue # only bother with what has been proven
            #if prover.impliedParent != None and (not prover.stmtToProve in prover.impliedParent.stmtToProve.provingStatements(set(prover.impliedParent.assumptions))):
            #    continue # only go with what is known
            if self._completesProofTree(prover, pvr2step):
                assert self.children != None, 'DerivationStep proof tree should have been made.'
                return True
            if not self._proverIsLeaf(prover):
                prover.appendProvers(breadth1stQueue)
        return False
    
    def _proverIsLeaf(self, prover):
        stmt = prover.stmtToProve
        if stmt.isAxiom():
            return True # by axiom
        elif stmt in prover.assumptions:
            return True # by assumption
        elif stmt.isTheorem() and stmt.getRegisteredVar() != None and stmt.proofNumber < self.proofNumber:
            return True # aliased theorem with a lesser proof number
        return False
    
    def _completesProofTree(self, prover, pvr2step):
        if self._proverIsLeaf(prover):
            pvr2step[prover] = self._makeDescendant([prover])
            while all([corequisite in pvr2step for corequisite in prover.corequisites]):
                children = [pvr2step[corequisite] for corequisite in prover.corequisites]
                prover = prover.impliedParent
                if prover == self.provers[0]:
                    self._setChildren(children)
                    self.howProven = self.children[0].stepType
                    return True # made it to what we were trying to prove
                step = self._makeDescendant([prover])
                step._setChildren(children)
                step.howProven = step.children[0].stepType
                pvr2step[prover] = step
        return False
            
    def numChildren(self):
        self.makeChildren()
        return len(self.children)
        
    def getChild(self, row):
        self.makeChildren()
        return self.children[row]

class SvgWidgetModel(QtCore.QAbstractItemModel):
    def __init__(self):
        QtCore.QAbstractItemModel.__init__(self)
        self.__view = None
    
    def setView(self, view):
        self.__view = view
            
    def makeSvgWidget(self, idx, svgData):
        if not self.holdsSvgWidget(idx):
            svgWidget = QtSvg.QSvgWidget()
            svgWidget.load(svgData)
            layout = QtGui.QHBoxLayout()
            layout.addWidget(svgWidget)
            layout.addStretch()
            layout.setContentsMargins(0, 0, 0, 0)
            widget = QtGui.QFrame()
            widget.setLayout(layout)
            widget.adjustSize()
            self.__view.setIndexWidget(idx, widget)
    
    def holdsSvgWidget(self, idx):
        return self.__view.indexWidget(idx) != None
    
    def getDisplayData(self, idx, obj):        
        pass # must override    
    
    def createIndex(self, row, column, obj):
        idx = QtCore.QAbstractItemModel.createIndex(self, row, column, obj)
        displayData = self.data(idx, QtCore.Qt.DisplayRole)        
        if isinstance(displayData, QtCore.QByteArray):
            self.makeSvgWidget(idx, displayData)
        return idx
        
class DerivationModel(SvgWidgetModel):
    COLUMNS = ['Statement', 'Assumptions', 'Step Type', 'How Proven', 'Context', 'Proven']
    
    def __init__(self):
        SvgWidgetModel.__init__(self)
        self.topLevelProvers = set()
        self.topLevelProofNumbers = []
        self.topLevels = [] # DerivationStep's
    
    def addTopLevel(self, prover, onlyEssentialSteps=True):
        '''
        Adds a prover at the top level if it doesn't already exist.
        '''
        if not prover in self.topLevelProvers:
            # sort the topLevels by proofNumber
            row = bisect_left(self.topLevelProofNumbers, prover.stmtToProve.proofNumber)
            self.beginInsertRows(QtCore.QModelIndex(), row, row)
            self.topLevelProofNumbers.insert(row, prover.stmtToProve.proofNumber)
            self.topLevels.insert(row, DerivationStep([prover], onlyEssentialSteps))
            self.topLevelProvers.add(prover)
            self.endInsertRows()
        
    def headerData(self, section, orientation, role=QtCore.Qt.DisplayRole):
        if orientation == QtCore.Qt.Horizontal and role == QtCore.Qt.DisplayRole:
            return self.COLUMNS[section]
        return None        

    def columnCount(self, parent_idx):
        return len(self.COLUMNS)
            
    def rowCount(self, parent_idx):
        if not parent_idx.isValid():
            return len(self.topLevels)
        return parent_idx.internalPointer().numChildren() 
        
    def index(self, row, column, parent_idx = QtCore.QModelIndex()):
        if not parent_idx.isValid():
            return self.createIndex(row, column, self.topLevels[row])
        step = parent_idx.internalPointer().getChild(row)
        return self.createIndex(row, column, step)
    
    def topLevelIndex(self, prover):
        '''
        Returns the index of a top-level item corresponding with the given prover.
        '''
        row = bisect_left(self.topLevelProofNumbers, prover.stmtToProve.proofNumber)
        while row < len(self.topLevels) and self.topLevels[row].proofNumber == prover.stmtToProve.proofNumber:
            if self.topLevels[row].provers[0] == prover:
                return self.index(row, 0)
            row += 1
        return None
        
    def getDisplayData(self, idx, step):        
        return step.getDisplayData(self.COLUMNS[idx.column()])
        
    def data(self, index, role = QtCore.Qt.DisplayRole):
        if not index.isValid():
            return None
        step = index.internalPointer()
        columnName = self.COLUMNS[index.column()]
        if role == QtCore.Qt.DisplayRole:
            if self.holdsSvgWidget(index):
                return None
            return step.getDisplayData(columnName)
        elif role == QtCore.Qt.UserRole:
            return step.getData(columnName)
        return None
    
    def parent(self, child_index):
        if not child_index.isValid():
            return QtCore.QModelIndex()
        step = child_index.internalPointer()
        if step in self.topLevels:
            return QtCore.QModelIndex()
        parent_obj = step.parent
        if parent_obj in self.topLevels:
            return self.createIndex(self.topLevels.index(parent_obj), 0, parent_obj)
        grandparent = parent_obj.parent
        row = grandparent.children.index(parent_obj)
        return self.createIndex(row, 0, parent_obj)

class AxiomModel(SvgWidgetModel):
    COLUMNS = ['Context/Name', 'Statement']
    
    def __init__(self):
        SvgWidgetModel.__init__(self)
        self._contexts = dict() # map context name to context
        self._axioms = dict() # map context to axiom list

    def addAxiom(self, axiom):
        context = axiom.statement.getRegisteredContext()
        self._contexts[context.getName()] = context
        self._axioms.setdefault(context, list()).append(axiom)
    
    def headerData(self, section, orientation, role=QtCore.Qt.DisplayRole):
        if orientation == QtCore.Qt.Horizontal and role == QtCore.Qt.DisplayRole:
            return self.COLUMNS[section]
        return None        

    def columnCount(self, parent_idx):
        return len(self.COLUMNS)
            
    def rowCount(self, parent_idx):
        if not parent_idx.isValid():
            return len(self._contexts)
        indexPtr = parent_idx.internalPointer()
        if isinstance(indexPtr, Context):
            return len(self._axioms[indexPtr])
        return 0
        
    def index(self, row, column, parent_idx = QtCore.QModelIndex()):
        if not parent_idx.isValid():
            return self.createIndex(row, column, self._contexts.values()[row])
        context = parent_idx.internalPointer()
        return self.createIndex(row, column, self._axioms[context][row])

    def data(self, index, role = QtCore.Qt.DisplayRole):
        if not index.isValid():
            return None
        indexPtr = index.internalPointer()
        columnName = self.COLUMNS[index.column()]
        data = None
        if isinstance(indexPtr, Context) and columnName != 'Statement':
            data = indexPtr
        elif isinstance(indexPtr, Expression):
            if columnName == 'Statement':
                data = indexPtr.statement
            else:
                data = indexPtr.statement.getRegisteredVar()
        if role == QtCore.Qt.UserRole:
            return data
        elif role == QtCore.Qt.DisplayRole:
            if self.holdsSvgWidget(index):
                return None
            if data == None:
                return ''
            if isinstance(data, Statement):
                return renderedExpr(data.getExpression())
            return str(data)
        return None
    
    def parent(self, child_index):
        if not child_index.isValid():
            return QtCore.QModelIndex()
        indexPtr = child_index.internalPointer()
        if isinstance(indexPtr, Context):
            return QtCore.QModelIndex()
        elif isinstance(indexPtr, Expression):
            context = indexPtr.statement.getRegisteredContext()
            return self.createIndex(self._contexts.keys().index(context.getName()), 0, context)
    
class ExpressionTreeNode:
    def __init__(self, expr, role, parent = None):
        self.expr = expr
        self.role = role
        self.parent = parent
        self.children = []
        if isinstance(expr, OperationOverInstances):
            self.children.append(ExpressionTreeNode(expr.operator, 'Operator', self))
            self.children.append(ExpressionTreeNode(expr.instanceVar, 'Instance Variable', self))
            self.children.append(ExpressionTreeNode(expr.instanceExpression, 'Instance Expression', self))
            if expr.condition != None:
                self.children.append(ExpressionTreeNode(expr.condition, 'Condition', self))
        elif isinstance(expr, Operation):
            self.children.append(ExpressionTreeNode(expr.operator, 'Operator', self))
            for operand in expr.operands:
                self.children.append(ExpressionTreeNode(operand, 'Operand', self))        
        
class ExpressionTreeModel(SvgWidgetModel):
    COLUMNS = ['Expression', 'Role', 'Type', 'Core Type', 'Context']
    
    def __init__(self, exprNodes):
        SvgWidgetModel.__init__(self)
        self.exprNodes = exprNodes
    
    def headerData(self, section, orientation, role=QtCore.Qt.DisplayRole):
        if orientation == QtCore.Qt.Horizontal and role == QtCore.Qt.DisplayRole:
            return self.COLUMNS[section]
        return None        

    def columnCount(self, parent_idx):
        return len(self.COLUMNS)
            
    def rowCount(self, parent_idx):
        if not parent_idx.isValid():
            return len(self.exprNodes)
        exprNode = parent_idx.internalPointer()
        return len(exprNode.children)
        
    def index(self, row, column, parent_idx):
        if not parent_idx.isValid():
            return self.createIndex(row, column, self.exprNodes[row])
        exprNode = parent_idx.internalPointer()
        return self.createIndex(row, column, exprNode.children[row])
        
    def data(self, index, role = QtCore.Qt.DisplayRole):
        if not index.isValid():
            return None
        exprNode = index.internalPointer()
        expr = exprNode.expr
        columnName = self.COLUMNS[index.column()]
        obj = None
        if columnName == 'Expression':
            obj = expr
        elif columnName == 'Role':
            obj = exprNode.role
        elif columnName == 'Type':
            obj = expr.__class__
        elif columnName == 'Core Type':
            if isinstance(expr, Literal):
                obj = Literal
            elif isinstance(expr, Variable):
                obj = Variable
            elif isinstance(expr, OperationOverInstances):
                obj = OperationOverInstances
            elif isinstance(expr, Operation):
                obj = Operation
        elif columnName == 'Context':
            if isinstance(expr, Literal):
                obj = expr.context
            elif expr.statement != None:
                obj = expr.statement.getRegisteredContext()
        if role == QtCore.Qt.UserRole:
            return obj
        if role == QtCore.Qt.DisplayRole:
            if obj == None:
                return 'N/A'
            if isinstance(obj, Expression):
                if self.holdsSvgWidget(index):
                    return None
                return renderedExpr(obj)
            return str(obj)

    def parent(self, child_index):
        if not child_index.isValid():
            return QtCore.QModelIndex()
        exprNode = child_index.internalPointer()
        if exprNode in self.exprNodes:
            return QtCore.QModelIndex()
        parentNode = exprNode.parent
        if parentNode in self.exprNodes:
            return self.createIndex(self.exprNodes.index(parentNode), 0, parentNode)
        grandparentNode = parentNode.parent
        row = grandparentNode.children.index(parentNode)
        return self.createIndex(row, 0, parentNode)

class DerivationTreeView(QtGui.QTreeView):
    def __init__(self, parent, model):
        QtGui.QTreeView.__init__(self, parent)
        self.parent = parent
        self.history = []
        self.model = model
        self.setModel(model)

    def keyPressEvent(self, event):
        selectedStep = self.parent.selection_idx.internalPointer()
        if event.key() == QtCore.Qt.Key_Left and selectedStep.isRoot() and not self.isExpanded(self.parent.selection_idx):
            self.setCurrentIndex(self.history.pop())
        elif event.key() == QtCore.Qt.Key_Right and selectedStep.isAliasLink():
            prover = selectedStep.parent.getStatement().getOrMakeProver()
            self.model.addTopLevel(prover)
            self.history.append(self.currentIndex())
            self.setCurrentIndex(self.model.topLevelIndex(prover))
        else:
            QtGui.QTreeView.keyPressEvent(self, event)        

class DerivationTreeViewer(QtGui.QWidget):
    def __init__(self, provers, onlyEssentialSteps=True, showExpressionTree=True):
        QtGui.QWidget.__init__(self)
        x, y, w, h = 300, 300, 1400, 500
        self.setGeometry(x, y, w, h)

        derivationModel = DerivationModel()
        self.derivationTV = DerivationTreeView(self, derivationModel)
        derivationModel.setView(self.derivationTV)
        for prover in provers:
            derivationModel.addTopLevel(prover, onlyEssentialSteps=onlyEssentialSteps)
        self.derivationTV.setColumnWidth(0, 600)
        self.derivationTV.setColumnWidth(1, 300)
        self.selectModel = self.derivationTV.selectionModel()
        self.selectModel.currentRowChanged.connect(self.currentRowChanged)
        self.derivationTV.doubleClicked.connect(self.doubleClick)

        layout = QtGui.QVBoxLayout()
        layout.addWidget(self.derivationTV)

        if showExpressionTree:
            exprModel = ExpressionTreeModel([])
            self.exprTV = QtGui.QTreeView(self)
            self.exprTV.setModel(exprModel)
            exprModel.setView(self.exprTV)
            self.exprTV.setColumnWidth(0, 600)
            self.exprTV.setColumnWidth(1, 150)
            self.exprTV.setColumnWidth(2, 150)
            self.exprTV.setColumnWidth(3, 200)
            layout.addWidget(self.exprTV)
        else:
            self.exprTV = None
        
        self.setLayout(layout)
        self.selection_idx = None
    
    def currentRowChanged(self, current_idx, prev_idx):
        self.selection_idx = current_idx
        selection = self.selection_idx.internalPointer()
        stmts = [prover.stmtToProve for prover in selection.provers]
        stmtNodes = [ExpressionTreeNode(stmt.getExpression(), 'Statement') for stmt in stmts]
        assumptionNodes = [ExpressionTreeNode(assumption.getExpression(), 'Assumption') for assumption in selection.getAssumptions()]
        if self.exprTV != None:
            exprModel = ExpressionTreeModel(stmtNodes+assumptionNodes)
            self.exprTV.setModel(exprModel)
            exprModel.setView(self.exprTV)
    
    def doubleClick(self):
        print "double-clicked"
        selection = self.selection_idx.internalPointer()
        #selection.children = None
        #selection.onlyEssentialSteps = True

        
        #self.selection_model = self.tv.selectionModel()
        #self.selection_model.currentRowChanged.connect(self.current_row_changed)

class AxiomTreeViewer(QtGui.QWidget):
    def __init__(self, axioms):
        QtGui.QWidget.__init__(self)
        x, y, w, h = 300, 300, 1000, 500
        self.setGeometry(x, y, w, h)

        axiomModel = AxiomModel()
        self.axiomTV = QtGui.QTreeView(self)
        self.axiomTV.setModel(axiomModel)
        axiomModel.setView(self.axiomTV)
        for axiom in axioms:
            axiomModel.addAxiom(axiom)
        self.axiomTV.setColumnWidth(0, 300)
        layout = QtGui.QVBoxLayout()
        layout.addWidget(self.axiomTV)
        self.setLayout(layout)
    
    
qa = QtGui.QApplication(sys.argv)
def showTreeView(stmtsOrProvers, onlyEssentialSteps=True, showExpressionTree=True):
    """
    Take in a list of statements, list of provers, single statement, or single prover
    as stmtsOrProvers.
    """
    try:
        provers = []
        for stmtOrProver in stmtsOrProvers:
            if isinstance(stmtOrProver, Statement):
                provers.append(stmtOrProver.getOrMakeProver())
            elif isinstance(stmtOrProver, Statement.Prover):
                provers.append(stmtOrProver)
        app = DerivationTreeViewer(provers, onlyEssentialSteps, showExpressionTree)
        app.show()
        qa.exec_()
    except TypeError:
        # handle single item passed in instead of list
        showTreeView([stmtsOrProvers], onlyEssentialSteps)

def showAxioms(axioms):
    app = AxiomTreeViewer(axioms)
    app.show()
    qa.exec_()

if __name__ == "__main__":
    import booleans
    booleans.booleans.deriveAll()
    #boolTheorems = {var.statement for varName, var in vars(booleans.booleans).iteritems() if isinstance(var, Expression) and var.statement != None and var.statement.isTheorem()}
    #showTreeView(boolTheorems, True)
    showTreeView(booleans.booleans.hypotheticalDisjunction.statement, True)
