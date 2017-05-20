'''
Define some custom magic for Prove-It in IPython notebooks.
'''

from IPython.core.magic import Magics, magics_class, line_magic, register_line_magic
from IPython import get_ipython
from proveit._core_.expression import Expression
from proveit._core_.context import Context
import new
import re
import os

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
        shell.ex("from proveit._core_.magics import SpecialExpression")
        self._setBehavior(lambda lhs: "SpecialExpression('%s', %s)"%(lhs,lhs))
    

assignmentBehaviorModifier = AssignmentBehaviorModifier()


@magics_class
class ProveItMagic(Magics):
    "Magics that hold additional state"

    def __init__(self, shell):
        # You must call the parent constructor
        super(ProveItMagic, self).__init__(shell)
        self.kind = None
        self.definitions = dict()
        self.lowerCaseNames = set()
    
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
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_axioms (or %begin_theorems) once per IPython session.")
        self._set_package(line)
        print "Defining axioms for package '" + self.package + "'"
        print "Subsequent end-of-cell assignments will define axioms"
        print "%end_axioms will finalize the definitions"
        assignmentBehaviorModifier.specialStatements(self.shell)
        self.kind = 'axioms'

    @line_magic
    def end_axioms(self, line):
        self.finish('axioms')

    @line_magic
    def begin_theorems(self, line):
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_theorems (or %begin_axioms) once per IPython session.")
        self._set_package(line)
        print "Defining theorems for package '" + self.package + "'"
        print "Subsequent end-of-cell assignments will define theorems"
        print "%end_theorems will finalize the definitions"
        assignmentBehaviorModifier.specialStatements(self.shell)
        self.kind = 'theorems'

    @line_magic
    def end_theorems(self, line):
        self.finish('theorems')
    
    @line_magic
    def begin_common(self, line):
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_common once per IPython session.")
        self._set_package(line)
        print "Defining common sub-expressions for package '" + self.package + "'"
        print "Subsequent end-of-cell assignments will define common sub-expressions"
        print "%end_common will finalize the definitions"
        assignmentBehaviorModifier.specialStatements(self.shell)
        self.kind = 'common'

    @line_magic
    def end_common(self, line):
        self.finish('common')
                
    @line_magic
    def begin_proof(self, line):
        assignmentBehaviorModifier.displayAssignment()
        pass

    def finish(self, kind):
        '''
        Finish 'axioms', 'theorems', or 'common' for the Context
        associated with the current working directory.
        '''
        if self.kind != kind:
            raise ProveItMagicFailure("Must run %begin_%s before %end_%s"%(kind,kind))
        context = Context() # context based upon current working directory
        # Add the special statements to the certified database
        if kind=='axioms':
            context._setAxioms(self.definitions)
        elif kind=='theorems':            
            context._setTheorems(self.definitions)
        elif kind=='common':
            context._setCommonExpressions(self.definitions)
        specialStatementsClassName = kind[0].upper() + kind[1:]
        if kind=='common': specialStatementsClassName = 'CommonExpressions'
        # make an _axioms_.py or _theorems_.py file for importing axioms/theorems
        # from the certified database.
        output = "import sys\n"
        output += "from proveit._core_.context import Context, %s\n"%specialStatementsClassName
        output += "sys.modules[__name__] = %s(Context(__file__))\n"%(specialStatementsClassName)
        if os.path.isfile('_%s_.py'%kind):
            with open('_%s_.py'%kind, 'r') as f:
                if f.read() != output:
                    raise ProveItMagicFailure("An existing _%s_.py must be removed before a proper one may be autogenerated"%kind)
        else:        
            with open('_%s_.py'%kind, 'w') as f:
                f.write(output)
        if kind=='common':
            print "Common expressions may be imported from autogenerated _%s_.py"%kind
        else:
            print "%s may be imported from autogenerated _%s_.py"%(specialStatementsClassName, kind)

class SpecialExpression:    
    def __init__(self, name, expr):
        if not isinstance(expr, Expression):
            raise ValueError("Right hand side of the special statement must be an Expression")
        if proveItMagic.kind == 'axioms' or proveItMagic.kind == 'theorems':
            if name.lower() in proveItMagic.lowerCaseNames:
                raise ProveItMagicFailure("%s names must be unique regardless of capitalization"%SpecialExpression.kind[:-1])
        self.name = name
        self.expr = expr
        proveItMagic.lowerCaseNames.add(name.lower())
        proveItMagic.definitions[name] = expr

    def _repr_html_(self):
        return '<strong>' + self.name + '</strong>: ' + self.expr._repr_html_()

# This class must then be registered with a manually created instance,
# since its constructor has different arguments from the default:
ip = get_ipython()
proveItMagic = ProveItMagic(ip)
ip.register_magics(proveItMagic)

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
