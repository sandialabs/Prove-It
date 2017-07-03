'''
Define some custom magic for Prove-It in IPython notebooks.
'''

from IPython.core.magic import Magics, magics_class, line_magic
from IPython import get_ipython
from proveit._core_.expression import Expression
from proveit._core_.context import Context
import ipywidgets as widgets
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

    def displayAssignments(self, shell):
        shell.ex("from proveit._core_.magics import Assignments")
        self._setBehavior(lambda varnames: "Assignments([" + ','.join("'%s'"%varname for varname in varnames) + "], [" + ','.join(varnames) + "])")

class SubContexts(widgets.VBox):
    '''
    A Jupyter VBox widget for editing the list of sub-contexts of a context and their descriptions.
    '''
    def __init__(self):
        widgets.VBox.__init__(self, [])
        if not os.path.isfile('_sub_contexts_.txt'):
            open('_sub_contexts_.txt', 'w')
        self.smallButtonLayout = widgets.Layout(width='30px')
        self.subContextLinkLayout = widgets.Layout(width='20%')
        self.subContextDescriptionLayout = widgets.Layout(width='100%')
        self.subContexts = []
        self.subContextDescriptions = dict()
        with open('_sub_contexts_.txt') as f:
            for line in f.readlines():
                sub_context_name = line.strip()
                self.subContexts.append(sub_context_name)
                self._addSubContextRow(sub_context_name)
    
    def _addSubContextRow(self, subContextName):
        subContextDescription = self.readDescription(subContextName)
        small_button_layout = self.smallButtonLayout
        sub_context_link_layout = self.subContextLinkLayout
        sub_context_description_layout = self.subContextDescriptionLayout
        #rename_button =  widgets.Button(description='', disabled=False, button_style='', tooltip='rename', icon='pencil', layout=small_button_layout)
        up_button = widgets.Button(description='', disabled=False, button_style='', tooltip='move up', icon='chevron-up', layout=small_button_layout)
        dn_button = widgets.Button(description='', disabled=False, button_style='', tooltip='move down', icon='chevron-down', layout=small_button_layout)
        def moveUp(sender):
            idx = self.subContexts.index(subContextName)
            self.moveUp(idx)
        def moveDown(sender):
            idx = self.subContexts.index(subContextName)
            self.moveUp(idx+1)
        up_button.on_click(moveUp)
        dn_button.on_click(moveDown)
        delete_button = widgets.Button(description='', disabled=False, button_style='danger', tooltip='delete context', icon='trash', layout=small_button_layout)
        href = self.subContextNotebook(subContextName)
        sub_context_link = widgets.HTML('<a href="%s" target="_blank">%s</a>'%(href,subContextName) , layout=sub_context_link_layout)
        sub_context_description = widgets.Text(value=subContextDescription, placeholder='Add a brief description here...', layout=sub_context_description_layout)
        def setDescription(change):
            self.subContextDescriptions[subContextName] = change['new']
            self.writeDescriptionFile(subContextName)
        sub_context_description.observe(setDescription, names='value')
        self.children = self.children + (widgets.HBox([sub_context_link, sub_context_description, up_button, dn_button, delete_button]),)
        #self.children = self.children + (widgets.HBox([sub_context_link, rename_button, sub_context_description, up_button, dn_button, delete_button]),)
    
    def subContextNotebook(self, subContextName):
        '''
        Returns the path of the _context_.ipynb notebook for the given sub-context,
        creating it if necessary.
        '''
        import proveit
        import json
        notebook_name = os.path.join(subContextName, '_context_.ipynb')
        if not os.path.isdir(subContextName):
            os.mkdir(subContextName)
            init_name = os.path.join(subContextName, '__init__.py')
            open(init_name, 'w')
        if os.path.isfile(notebook_name):
            # already exists
            return notebook_name
        proveit_path = os.path.split(proveit.__file__)[0]
        with open(os.path.join(proveit_path, '..', '_context_template_.ipynb'), 'r') as template:
            nb = template.read()
            sub_context = Context(subContextName)
            context_name_segments = sub_context.name.split('.')
            context_html_segments = []
            for k, context_name_segment in enumerate(context_name_segments[:-1]):      
                href = os.path.join(*(['..']*(len(context_name_segments) - k - 1) + ['_context_.ipynb']))
                context_html_segments.append(r'<a href=\"%s\">%s</a>'%(json.dumps(href).strip('"'), context_name_segment))
            context_html_segments.append(context_name_segments[-1])
            nb = nb.replace('#CONTEXT#', '.'.join(context_html_segments))
        # write the notebook file
        with open(notebook_name, 'w') as notebook_file:
            notebook_file.write(nb)
        return notebook_name        
    
    def addSubContext(self, subContextName):
        if subContextName in self.subContexts:
            return
        with open('_sub_contexts_.txt', 'a') as f:
            f.write(subContextName + '\n')
            self._addSubContextRow(subContextName)
    
    def moveUp(self, i):
        if i<=0 or i==len(self.children): return # can't move the first entry up or go beyond the last entry
        self.children = self.children[:i-1] + (self.children[i], self.children[i-1]) + self.children[i+1:]
        self.subContexts = self.subContexts[:i-1] + [self.subContexts[i], self.subContexts[i-1]] + self.subContexts[i+1:]
        self.rewriteSubContextTxt()

    def readDescription(self, subContextName):
        brief_description = ''
        brief_description_filename = os.path.join(subContextName, '_brief_description_.txt')
        if os.path.isfile(brief_description_filename):
            with open(brief_description_filename) as f2:
                brief_description = f2.read().strip()
        self.subContextDescriptions[subContextName] = brief_description
        return brief_description

    def writeDescriptionFile(self, subContextName):
        brief_description = self.subContextDescriptions[subContextName]
        if brief_description != '':
            brief_description_filename = os.path.join(subContextName, '_brief_description_.txt')
            with open(brief_description_filename, 'w') as f:
                f.write(brief_description + '\n')

    def rewriteSubContextTxt(self):
        # rewrite the sub_contexts.txt file with new information
        with open('_sub_contexts_.txt', 'w') as f:
            for sub_context_name in self.subContexts:
                f.write(sub_context_name + '\n')    

@magics_class
class ProveItMagic(Magics):
    "Magics that hold additional state"

    def __init__(self, shell):
        # You must call the parent constructor
        super(ProveItMagic, self).__init__(shell)
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
            self.assignmentBehaviorModifier.displayAssignments(self.shell)
    
    @line_magic
    def context(self, line):
        '''
        Create the _common_, _axioms_ and _theorems_ notebooks for the current
        context (if they do not already exist).  Show the table of contents
        for sub-contexts which may be edited.
        '''
        import proveit
        import ipywidgets as widgets
        context = Context()
        proveit_path = os.path.split(proveit.__file__)[0]
        special_notebook_types = ('common', 'axioms', 'theorems')
        special_notebook_text = ('common expressions', 'axioms', 'theorems')
        for special_notebook_type in special_notebook_types:
            notebook_name = '_%s_.ipynb'%special_notebook_type
            if not os.path.isfile(notebook_name):
                # notebook does not yet exist, create it from the template
                template_name = '_%s_template_.ipynb'%special_notebook_type
                with open(os.path.join(proveit_path, '..', template_name), 'r') as template:
                    nb = template.read()
                    nb = nb.replace('#CONTEXT#', context.name)
                    nb = nb.replace('#CONTEXT_LINK#', '_context_.ipynb')
                # write the notebook file
                with open(notebook_name, 'w') as notebook_file:
                    notebook_file.write(nb)
        special_notebook_links = []
        full_width_layout = widgets.Layout(width='100%', padding='5px')
        for special_notebook_type, special_notebook_text in zip(special_notebook_types, special_notebook_text):
            special_notebook_links.append(widgets.HTML('<a href="_%s_.ipynb" target="_blank">%s</a>'%(special_notebook_type, special_notebook_text), layout=full_width_layout))
            
        sub_contexts_label = widgets.Label('List of sub-contexts:', layout = widgets.Layout(width='100%'))
        sub_contexts = SubContexts()
        #sub_context_widgets = widgets.VBox(sub_context_widgets)
        add_context_widget = widgets.Text(value='', placeholder='Add sub-context...')
        def addSubContext(sender):
            sub_contexts.addSubContext(add_context_widget.value)
            add_context_widget.value = ''
        add_context_widget.on_submit(addSubContext)
        return widgets.VBox([widgets.HBox(special_notebook_links), sub_contexts_label, sub_contexts, add_context_widget])
    
    @line_magic
    def begin_axioms(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_axioms (or %begin_theorems) once per IPython session.")
        print "Defining axioms for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define axioms"
        print "%end_axioms will finalize the definitions"
        self.kind = 'axiom'

    @line_magic
    def end_axioms(self, line):
        self.finish('axiom')

    @line_magic
    def begin_theorems(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_theorems (or %begin_axioms) once per IPython session.")
        print "Defining theorems for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define theorems"
        print "%end_theorems will finalize the definitions"
        self.kind = 'theorem'

    @line_magic
    def end_theorems(self, line):
        self.finish('theorem')
    
    @line_magic
    def begin_common(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            raise ProveItMagicFailure("May only run %begin_common once per IPython session.")
        print "Defining common sub-expressions for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define common sub-expressions"
        print "%end_common will finalize the definitions"
        self.kind = 'common'

    @line_magic
    def end_common(self, line):
        self.finish('common')

    @line_magic
    def check_expr(self, line):
        _, hash_id = os.path.split(os.path.abspath('.'))
        context = Context()
        if self.shell.user_ns['expr'] != context.getStoredExpr(hash_id):
            raise ProveItMagicFailure("The build 'expr' does not match the stored Expression")
        print "Passed sanity check: built 'expr' is the same as the stored Expression."
                                
    @line_magic
    def begin_proof(self, line):
        sys.path.append('..')
        return Context('..').getTheorem(str(line.strip())).beginProof()

    def finish(self, kind):
        '''
        Finish 'axiom's, 'theorem's, or 'common' for the Context
        associated with the current working directory.
        '''
        if self.kind != kind:
            raise ProveItMagicFailure("Must run %begin_%s before %end_%s"%(kind,kind))
        # Add the special statements / expressions to the context
        context = self.context
        if kind=='axiom':
            context._setAxioms(self.definitions)
        elif kind=='theorem':            
            context._setTheorems(self.definitions)
        elif kind=='common':
            context._setCommonExpressions(self.definitions)

        # Update the expression notebooks now that these have been registered
        # as special expressions.
        for name, expr in self.definitions.iteritems():
            # remake the expression notebooks using the special expressions of the context
            context.expressionNotebook(expr)           
        print "Expression notebooks have been updated"

        # Make an _axioms_.py or _theorems_.py file for importing axioms/theorems
        # from the certified database.
        specialStatementsClassName = kind[0].upper() + kind[1:]
        if kind=='common': specialStatementsClassName = 'CommonExpressions'        
        output = "import sys\n"
        output += "from proveit._core_.context import Context, %s\n"%specialStatementsClassName
        output += "sys.modules[__name__] = %s(__file__)\n"%(specialStatementsClassName)        
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

class Assignments:    
    def __init__(self, names, rightSides):
        self.allExpressions = True
        for rightSide in rightSides:
            if not isinstance(rightSide, Expression):
                if proveItMagic.kind is not None:
                    raise ValueError("Right hand side of end-of-cell assignment(s) is expected to be Expression(s)")
                else:
                    self.allExpressions = False
        self.names = list(names)
        self.rightSides = list(rightSides)
        for name, rightSide in zip(names, rightSides):
            if proveItMagic.kind == 'axiom' or proveItMagic.kind == 'theorem':
                if name.lower() in proveItMagic.lowerCaseNames:
                    if not(proveItMagic.ranFinish and name in proveItMagic.definitions): # allowed to come back around after it finished once
                        raise ProveItMagicFailure("%s names must be unique regardless of capitalization"%proveItMagic.kind[:-1])
            proveItMagic.lowerCaseNames.add(name.lower())
            proveItMagic.definitions[name] = rightSide
    
    def html_line(self, name, rightSide):
        lhs_html = name
        if proveItMagic.kind == 'theorem':
            proofNotebook = proveItMagic.context.proofNotebook(name)
            lhs_html = '<a href="%s" target="_blank">%s</a>'%(os.path.relpath(proofNotebook), lhs_html)
        unofficialNameKindContext = None
        if proveItMagic.kind is not None:
            unofficialNameKindContext = (name, proveItMagic.kind, proveItMagic.context)
        rightSideStr = None
        if isinstance(rightSide, Expression):
            rightSideStr = rightSide._repr_html_(unofficialNameKindContext=unofficialNameKindContext)
        elif hasattr(rightSide, '_repr_html_'):
            rightSideStr = rightSide._repr_html_()
        if rightSideStr is None:
            rightSideStr = str(rightSide)
            print rightSideStr
        return '<strong id="%s">%s:</strong> %s<br>'%(name, lhs_html, rightSideStr)

    def _repr_html_(self):
        if self.allExpressions:
            return '\n'.join(self.html_line(name, rightSide) for name, rightSide in zip(self.names, self.rightSides))
        
    def __repr__(self):
        return '\n'.join('%s: %s'%(name, repr(rightSide)) for name, rightSide in zip(self.names, self.rightSides))
        

# This class must then be registered with a manually created instance,
# since its constructor has different arguments from the default:
ip = get_ipython()
if ip is not None:
    proveItMagic = ProveItMagic(ip)
    assignmentBehaviorModifier = AssignmentBehaviorModifier()
    assignmentBehaviorModifier.displayAssignments(ip)
    ip.register_magics(proveItMagic)

class ProveItMagicFailure(Exception):
    def __init__(self, message):
        self.message = message
    def __str__(self):
        return self.message
