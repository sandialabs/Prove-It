'''
Define some custom magic for Prove-It in IPython notebooks.
'''

from IPython.core.magic import Magics, magics_class, line_magic, register_line_magic
from IPython import get_ipython
from special_statements import SpecialStatement
import new
import re

class AssignmentBehaviorModifier:
    def __init__(self):
        self.ipython = ipython = get_ipython()
        # prevent unwanted overwriting when the extension is reloaded
        if not hasattr(ipython, 'orig_run_cell'):
            # remember the original version of 'run_cell'
            ipython.orig_run_cell = ipython.run_cell
    
    def _setBehavior(self, assignmentFn):
        ipython = self.ipython
        def new_run_cell(self, raw_cell, *args, **kwargs):
            lines = raw_cell.split('\n')
            last_line = lines[-1]
            if re.match("[a-zA-Z_][a-zA-Z0-9_]*\s*=", last_line) is not None:
                lhs, rhs = last_line.split('=', 1)
                lines.append(assignmentFn(lhs.strip()))
            new_raw_cell = '\n'.join(lines)
            ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
        ipython.run_cell = new.instancemethod(new_run_cell, ipython)
    
    def resetBehavior(self):
        ipython = self.ipython
        ipython.run_cell = ipython.orig_run_cell

    def displayAssignment(self):
        self._setBehavior(lambda lhs: lhs)
    
    def specialStatements(self, shell):
        shell.ex("from proveit._core_.special_statements import SpecialStatement")
        self._setBehavior(lambda lhs: "SpecialStatement('%s', %s)"%(lhs,lhs))
    

assignmentBehaviorModifier = AssignmentBehaviorModifier()

@magics_class
class SpecialStatementsMagic(Magics):
    "Magics that hold additional state"

    def __init__(self, shell):
        # You must call the parent constructor
        super(SpecialStatementsMagic, self).__init__(shell)
        self.package = None
        self.special_statement_kind = None
    
    def _set_package(self, line):
        '''
        Set the package attribute as the given "line", if it is not empty.
        If it is empty, set it according to the current working directory 
        on up the chain as long as each directory has an __init__.py file.
        For example, if the current working directory is
        C:\users\wwitzel\Prove-It\packages\proveit\logic\equality,
        the package will be "proveit.logic.equality" (given that __init__.py
        is in the proveit, proveit\logic, and proveit\logic\equality
        directorys, but not in the packages directory above it).
        '''
        import os
        if len(line) > 0:
            self.package = line
        else:
            path = os.getcwd()
            self.package = ''
            while os.path.isfile(os.path.join(path, '__init__.py')):
                path, tail = os.path.split(path)
                self.package = tail + '.' + self.package
            if self.package == '':
                self.package = os.path.split(path)[1]
    
    @line_magic
    def begin_axioms(self, line):
        if len(SpecialStatement.definitions) > 0 or self.special_statement_kind is not None:
            raise ProveItMagicFailure("May only run %begin_axioms (or %begin-theorems) once per IPython session.")
        self._set_package(line)
        print "Defining axioms for package " + self.package
        print "Subsequent end-of-cell assignments will define axioms"
        print "%end_axioms will finalize the definitions"
        assignmentBehaviorModifier.specialStatements(self.shell)
        self.special_statement_kind = 'axioms'

    @line_magic
    def end_axioms(self, line):
        if self.special_statement_kind != 'axioms':
            raise ProveItMagicFailure("Must run %begin_axioms before %end_axioms")
        SpecialStatement.finish(self.package, 'axioms')

    @line_magic
    def begin_theorems(self, line):
        if len(SpecialStatement.definitions) > 0 or self.special_statement_kind is not None:
            raise ProveItMagicFailure("May only run %begin_theorems (or %begin_axioms) once per IPython session.")
        self._set_package(line)
        print "Defining theorems for package " + self.package
        print "Subsequent end-of-cell assignments will define theorems"
        print "%end_theorems will finalize the definitions"
        assignmentBehaviorModifier.specialStatements(self.shell)
        self.special_statement_kind = 'theorems'

    @line_magic
    def end_theorems(self, line):
        if self.special_statement_kind != 'theorems':
            raise ProveItMagicFailure("Must run %begin_theorems before %end_theorems")
        SpecialStatement.finish(self.package, 'theorems')
    
    @line_magic
    def begin_proof(self, line):
        assignmentBehaviorModifier.displayAssignment()
        pass

# This class must then be registered with a manually created instance,
# since its constructor has different arguments from the default:
ip = get_ipython()
specialStatementsMagic = SpecialStatementsMagic(ip)
ip.register_magics(specialStatementsMagic)

@register_line_magic
def display_assignment(line):
    if line.strip() == 'off':
        assignmentBehaviorModifier.resetBehavior()        
    else:
        assignmentBehaviorModifier.displayAssignment()

# Delete to avoid name conflicts for automagic to work
del display_assignment

class ProveItMagicFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
