'''
Allows one to retrieve axiom/theorem statements from dill files.
'''

import sys
import proveit
from proveit.statement import Statement

class SpecialStatementRetrieval:
    def __init__(self, filename): # should be some theorems.py or axioms.py
        import os
        self.filename = filename
        self.path, self.scriptname = os.path.split(self.filename)
        if self.path == '': self.path = '.'
        self.statementType = os.path.splitext(self.scriptname)[0] # theorems or axioms
    
    def __getattr__(self, name):
        # open the dill file corresponding to the axiom/theorem
        import os, dill
        try:
            with open(os.path.join(self.path, '__pv_it__', self.statementType, name + '.dill'), 'r') as f:
                try:
                    expr = dill.load(f)
                except ImportError as e:
                    raise Exception('ImportError when loading dill file (' + str(e) + ').  Be sure to use absolute import paths in ' + self.statementType + '.ipynb')
                package = os.path.relpath(self.path, os.path.join(os.path.split(proveit.__file__)[0], '..')).replace(os.path.sep, '.')
                if self.statementType == 'axioms':
                    Statement.state(expr, package, name, _isAxiom=True)
                if self.statementType == 'theorems':
                    Statement.state(expr, package, name, _isNamedTheorem=True)
                return expr
        except IOError:
            raise AttributeError('no such ' + self.statementType[:-1])
        
    def __dir__(self):
        import os
        attribs = []
        for fname in os.listdir(os.path.join(self.path, '__pv_it__', self.statementType)):
            if os.path.splitext(fname)[1] == '.pv_it':
                attribs.append(fname[:-6])
        return attribs
        
