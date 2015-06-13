import os
import re
import statement
from statement import Statement, Expression, ExpressionList, Literal, Variable, MultiVariable, Operation, Lambda
from prover import Prover
from array import array
import xml.etree.ElementTree as ET
from qedDocumentGenerator import DocumentGenerator

class Context:
    def __init__(self, contextModule, literals, axiomDefFn, theoremDefFn):
        """
        Create a Context given its python module, list of literals, a function that generates
        the axioms, and a function that generates the theorems.  For these axiom/theorem functions,
        they must return a tuple pair of (first_expression, definition_dictionary).  The dictionary
        maps names to expressions that define the axioms/theorems.  The dictionary can contain
        superfluous elements.  Excluded are non-Expression types, names starting with '_', and
        Expressions with creationNum values preceeding that of first_expression.
        """
        # map "unique" internal expression representations to corresponding statements
        # which can map to one or more equivalent expressions (that may have different
        # external representations)
        self.package = contextModule.__package__
        assert not self.package is None
        self.name = contextModule.__name__
        if self.name[:8] == 'proveit.': self.name = self.name[8:]
        print self.package
        print self.name
        for _, literal in literals.iteritems():
            literal.setContext(self)
        self.literals = dict(literals)
        self._axiomDefFn = axiomDefFn
        self._theoremDefFn = theoremDefFn
        self._axiomDict = None
        self._theoremDict = None
        self._axioms = None
        self._theorems = None
        self._docGen = DocumentGenerator()
        
    def getName(self):
        return self.name
    
    def getLiteral(self, name):
        return self._literals[name]

    def getAxiomDictionary(self):
        '''
        Returns the dictionary mapping axiom names to expressions in this Context.
        '''
        self._defineAxioms()
        return dict(self._axiomDict)        
    
    def getTheoremDictionary(self):
        '''
        Returns the dictionary mapping theorem names to expressions in this Context.
        '''
        self._defineTheorems()
        return dict(self._theoremDict) 
      
    def creationOrderAxiomNames(self):
        '''
        Returns the list of axiom names in the order that the axiom expression was
        created.
        '''
        axiomDict = self.getAxiomDictionary()
        return sorted(axiomDict.keys(), key=lambda name : axiomDict[name].creationNum)

    def creationOrderTheoremNames(self):
        '''
        Returns the list of axiom names in the order that the axiom expression was
        created.
        '''
        thmDict = self.getTheoremDictionary()
        return sorted(thmDict.keys(), key=lambda name : thmDict[name].creationNum)
      
    def qed(self, theoremName, theoremExpr):
        '''
        Provide the proof of a theorem.
        '''
        self._defineTheorems()
        assert(self._theoremDict[theoremName] == theoremExpr)
        theoremExpr.prove()
        print "Theorem " + self.name + '.' + theoremName + " has been proven."
        Prover.clearTemporaryProvers()
        self._docGen.makeTheoremRST(self, theoremName, theoremExpr)
    
    def __repr__(self):
        return self.name
    
    def _exprDefDictionary(self, firstExprAndDefinitions):
        if firstExprAndDefinitions is None: return # nothing defined
        firstExpr, definitions = firstExprAndDefinitions
        firstExprNum = firstExpr.creationNum
        for name, definition in definitions.iteritems():
            if isinstance(definition, Expression) and not name.startswith('_') and definition.creationNum >= firstExprNum:
                freeVars = definition.freeVars()
                assert len(freeVars) == 0, 'Expressions with free variable are not allowed as axioms or definitions: ' + name
                yield name, definition
    
    def _defineAxioms(self):
        if self._axioms is None:
            self._axiomDict = {name:axiom for name, axiom in self._exprDefDictionary(self._axiomDefFn())}
            self._axioms = set(self._axiomDict.values())

    def _defineTheorems(self):
        if self._theorems is None:
            self._theoremDict = {name:theorem for name, theorem in self._exprDefDictionary(self._theoremDefFn())}
            self._theorems = set(self._theoremDict.values())

    def __getattr__(self, name):
        '''
        When accessing an axiom or theorem, it needs to be defined and "stated" if it
        hadn't been already.
        '''
        if not name in self.__dict__:
            self._defineAxioms()
            self._defineTheorems()
            if name in self._axiomDict:
                axiom = self._axiomDict[name]
                self.__dict__[name] = axiom      
                return Statement.state(axiom, _context=self, _name=name, _isAxiom=True) 
            elif name in self._theoremDict:
                theorem = self._theoremDict[name]
                self.__dict__[name] = theorem
                return Statement.state(theorem, _context=self, _name=name, _isNamedTheorem=True) 
        else:
            return self.__dict__[name]
        raise AttributeError
    
    
    """
    def defineAxioms(self, axiomMap):
        html = ET.Element('html')
        h1 = ET.SubElement(html, 'h1')
        h1.text = self.contextModule.__package__ + "." + self.contextModule.__name__ + " axioms"
        dl = ET.SubElement(html, 'dl')
        for name, definition in axiomMap.iteritems():
            if isinstance(definition, Expression):
                print "add: ", name
                dt = ET.SubElement(dl, 'dt')
                dd = ET.SubElement(dl, 'dd')
                dt.text = name
                mathml = ET.SubElement(dd, 'math')
                parser = ET.XMLParser()
                print definition.formatted(statement.MATHML)
                parser.feed(definition.formatted(statement.MATHML))
                mathml.append(parser.close())
                if name in self._axioms:
                    # check that an axiom definition is consistent with what is already in the database
                    assert definition == self._axioms, 'Axiom definition inconsistent with database'
                else:
                    # make sure there isn't any other variable with this name in the contextModule dictionary
                    assert not name in self.contextModule.__dict__, "Axiom name not unique in the context's module"
                    # add the axiom definition to the database
                    self._addAxiom(name, definition)
        axiomsHTML = open('axioms.html', 'w')
        axiomsHTML.write(ET.tostring(html, method='html'))
        axiomsHTML.close()
    """

    def defineTheorems(self, module):
        for name, definition in module.locals().iteritems():
            if isinstance(definition, Expression):
                if name in self._theorems:
                    # check that an theorme definition is consistent with what is already in the database
                    assert definition == self._theorems, 'Theorem definition inconsistent with database'
                else:
                    # make sure there isn't any other variable with this name in the contextModule dictionary
                    assert not name in self.contextModule, "Theorem name not unique in the context's module"
                    # add the theorem definition to the database
                    self._addTheorem(name, definition)

    


'''
def registerTheorems(moduleName, variables):
    for vName, v in variables.iteritems():
        if isinstance(v, Expression) and v.statement != None and len(v.freeVars()) == 0:
            v.statement.registerPythonVar(PythonVar(moduleName, vName))
'''