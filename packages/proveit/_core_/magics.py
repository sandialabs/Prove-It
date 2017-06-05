'''
Define some custom magic for Prove-It in IPython notebooks.
'''

from IPython.core.magic import Magics, magics_class, line_magic
from IPython import get_ipython
from proveit._core_.expression import Expression
from proveit._core_.context import Context
import new
import re
import os
import sys

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
            # find the last non-indented python statement in the cell
            idx = [k for k, line in enumerate(lines) if len(line) > 0 and re.match("\s", line[0]) is None][-1]
            last_python_stmt = '\n'.join(lines[idx:])
            # look for one or more variables on the left side of an assignment
            if re.match("[a-zA-Z_][a-zA-Z0-9_]*\s*(,\s*[a-zA-Z_][a-zA-Z0-9_]*)*\s*=", last_python_stmt) is not None:
                lhs, rhs = last_python_stmt.split('=', 1)
                lines.append(assignmentFn([varname.strip() for varname in lhs.split(',') ]))
            new_raw_cell = '\n'.join(lines)
            ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
        ipython.run_cell = new.instancemethod(new_run_cell, ipython)
    
    def resetBehavior(self):
        ipython = self.ipython
        ipython.run_cell = ipython.orig_run_cell

    def displayAssignment(self, shell):
        shell.ex("from proveit._core_.magics import DisplayAssignment")
        self._setBehavior(lambda varnames: "DisplayAssignment(" + ', '.join(varnames) + ")")
    
    def specialStatements(self, shell):
        shell.ex("from proveit._core_.magics import SpecialExpressions")
        self._setBehavior(lambda varnames: "SpecialExpressions([" + ','.join("'%s'"%varname for varname in varnames) + "], [" + ','.join(varnames) + "])")

@magics_class
class ProveItMagic(Magics):
    "Magics that hold additional state"

    def __init__(self, shell, assignmentBehaviorModifier):
        # You must call the parent constructor
        super(ProveItMagic, self).__init__(shell)
        self.assignmentBehaviorModifier = assignmentBehaviorModifier
        self.kind = None
        self.definitions = dict()
        self.lowerCaseNames = set()
        self.context = None 
        self.ranFinish = False
    
    @line_magic
    def display_assignments(self, line):
        if line.strip() == 'off':
            self.assignmentBehaviorModifier.resetBehavior()        
        else:
            self.assignmentBehaviorModifier.displayAssignment(self.shell)
    
    @line_magic
    def begin_axioms(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_axioms (or %begin_theorems) once per IPython session.")
        print "Defining axioms for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define axioms"
        print "%end_axioms will finalize the definitions"
        self.assignmentBehaviorModifier.specialStatements(self.shell)
        self.kind = 'axioms'

    @line_magic
    def end_axioms(self, line):
        self.finish('axioms')

    @line_magic
    def begin_theorems(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_theorems (or %begin_axioms) once per IPython session.")
        print "Defining theorems for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define theorems"
        print "%end_theorems will finalize the definitions"
        self.assignmentBehaviorModifier.specialStatements(self.shell)
        self.kind = 'theorems'

    @line_magic
    def end_theorems(self, line):
        self.finish('theorems')
    
    @line_magic
    def begin_common(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_common once per IPython session.")
        print "Defining common sub-expressions for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define common sub-expressions"
        print "%end_common will finalize the definitions"
        self.assignmentBehaviorModifier.specialStatements(self.shell)
        self.kind = 'common'

    @line_magic
    def end_common(self, line):
        self.finish('common')
                
    @line_magic
    def begin_proof(self, line):
        self.assignmentBehaviorModifier.displayAssignment(self.shell)
        sys.path.append('..')
        return Context('..').getTheorem(str(line.strip())).beginProof()

    def finish(self, kind):
        '''
        Finish 'axioms', 'theorems', or 'common' for the Context
        associated with the current working directory.
        '''
        if self.kind != kind:
            raise ProveItMagicFailure("Must run %begin_%s before %end_%s"%(kind,kind))
        # Add the special statements / expressions to the context
        context = self.context
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
        self.ranFinish = True            

class DisplayAssignment:    
    def __init__(self, *assignments):
        self.assignments = list(assignments)

    def _repr_html_(self):
        return '\n'.join(((obj._repr_html_() if hasattr(obj, '_repr_html_') else repr(obj)) + '<br>') for obj in self.assignments)

class SpecialExpressions:    
    def __init__(self, names, exprs):
        for expr in exprs:
            if not isinstance(expr, Expression):
                raise ValueError("Right hand side of assignment is expected to be Expression(s)")
        self.names = list(names)
        self.exprs = list(exprs)
        for name, expr in zip(names, exprs):
            if proveItMagic.kind == 'axioms' or proveItMagic.kind == 'theorems':
                if name.lower() in proveItMagic.lowerCaseNames:
                    if not(proveItMagic.ranFinish and name in proveItMagic.definitions): # allowed to come back around after it finished once
                        raise ProveItMagicFailure("%s names must be unique regardless of capitalization"%proveItMagic.kind[:-1])
            proveItMagic.lowerCaseNames.add(name.lower())
            proveItMagic.definitions[name] = expr
    
    def html_line(self, name, expr):
        lhs_html = name
        if proveItMagic.kind == 'theorems':
            proofNotebook = proveItMagic.context.proofNotebook(name)
            lhs_html = '<a href="%s">%s</a>'%(os.path.relpath(proofNotebook), lhs_html)
        return '<strong id="%s">%s</strong>: %s<br>'%(name, lhs_html, expr._repr_html_())

    def _repr_html_(self):
        return '\n'.join(self.html_line(name, expr) for name, expr in zip(self.names, self.exprs))

# This class must then be registered with a manually created instance,
# since its constructor has different arguments from the default:
ip = get_ipython()
if ip is not None:
    assignmentBehaviorModifier = AssignmentBehaviorModifier()
    proveItMagic = ProveItMagic(ip, assignmentBehaviorModifier)
    ip.register_magics(proveItMagic)

class ProveItMagicFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
