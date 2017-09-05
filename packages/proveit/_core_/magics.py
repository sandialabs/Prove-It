'''
Define some custom magic for Prove-It in IPython notebooks.
'''

from IPython.core.magic import Magics, magics_class, line_magic
from IPython import get_ipython
from proveit._core_.expression import Expression
from proveit._core_ import KnownTruth
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
            non_indented_lines = [line for line in lines if len(line) > 0 and re.match("\s", line[0]) is None]
            if len(non_indented_lines)==0: 
                # no non-indented lines.  just run the cell normally.
                new_raw_cell = '\n'.join(lines)
                return ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
            # get the index of the last non-indented line
            idx = [k for k, line in enumerate(non_indented_lines)][-1]
            last_python_stmt = '\n'.join(lines[idx:])
            # look for one or more variables on the left side of an assignment
            if re.match("[a-zA-Z_][a-zA-Z0-9_]*\s*(,\s*[a-zA-Z_][a-zA-Z0-9_]*)*\s*=", last_python_stmt) is not None:
                lhs, rhs = last_python_stmt.split('=', 1)
                lines.append(assignmentFn([varname.strip() for varname in lhs.split(',') ]))
            new_raw_cell = '\n'.join(lines)
            return ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
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
    At first, a static html version will be displayed with just an "Edit" button at the bottom.
    When "Edit" is pressed, the html tables are made invisible via Javascript and the editable
    version of the table is presented.
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
            self.subContexts.append(subContextName)
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

    def __init__(self, shell, assignmentBehaviorModifier):
        # You must call the parent constructor
        super(ProveItMagic, self).__init__(shell)
        self.kind = None
        self.definitions = dict()
        self.keys = [] # the keys of the definitions in the order they appear
        self.lowerCaseNames = set()
        self.context = None 
        self.ranFinish = False
        self.assignmentBehaviorModifier = assignmentBehaviorModifier
        assignmentBehaviorModifier.displayAssignments(ip)
    
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
        from IPython.display import display, HTML
        # create an '_init_.py' in the directory if there is not an existing one.
        if not os.path.isfile('__init__.py'):
            open('__init__.py', 'w').close() # create an empty __init__.py
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
        #special_notebooks_html = '<table>'
        #for special_notebook_type, special_notebook_text in zip(special_notebook_types, special_notebook_text):
        #    special_notebooks_html += '<th><a href="_%s_.ipynb" target="_blank">%s</a></th>'%(special_notebook_type, special_notebook_text)
        #special_notebooks_html += '</table>'
        #display(HTML(special_notebooks_html))
        
        special_notebook_links = []
        full_width_layout = widgets.Layout(width='100%', padding='5px')
        for special_notebook_type, special_notebook_text in zip(special_notebook_types, special_notebook_text):
            special_notebook_links.append(widgets.HTML('<a href="_%s_.ipynb" target="_blank">%s</a>'%(special_notebook_type, special_notebook_text), layout=full_width_layout))
        special_notebook_links = widgets.HBox(special_notebook_links)
            
        sub_contexts_label = widgets.Label('List of sub-contexts:', layout = widgets.Layout(width='100%'))
        sub_contexts = SubContexts()
        #sub_context_widgets = widgets.VBox(sub_context_widgets)
        add_context_widget = widgets.Text(value='', placeholder='Add sub-context...')
        def addSubContext(sender):
            sub_contexts.addSubContext(add_context_widget.value)
            add_context_widget.value = ''
        add_context_widget.on_submit(addSubContext)
        #layout = widgets.Layout(display='flex', flex_flow='column-reverse')
        #display(widgets.Button(description='Edit...', disabled=False, button_style='', tooltip='Edit the sub-contents list', layout=layout))
        #layout = widgets.Layout(float='bottom')
        display(widgets.VBox([special_notebook_links, sub_contexts_label, sub_contexts, add_context_widget]))
    
    @line_magic
    def begin_axioms(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'axioms':
                raise ProveItMagicFailure("Run %begin_axioms in a separate notebook from %begin_%s."%self.kind)
            print "WARNING: Re-running %begin_axioms does not reset previously defined axioms."
            print "         It is suggested that you restart and run all cells after editing axioms."
        print "Defining axioms for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define axioms"
        print "%end_axioms will finalize the definitions"
        self.kind = 'axioms'

    @line_magic
    def end_axioms(self, line):
        self.finish('axioms')

    @line_magic
    def begin_theorems(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'theorems':
                raise ProveItMagicFailure("Run %begin_theorems in a separate notebook from %begin_%s."%self.kind)
            print "WARNING: Re-running %begin_theorems does not reset previously defined theorems."
            print "         It is suggested that you restart and run all cells after editing theorems."
        print "Defining theorems for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define theorems"
        print "%end_theorems will finalize the definitions"
        self.kind = 'theorems'

    @line_magic
    def end_theorems(self, line):
        self.finish('theorems')
        # stash proof notebooks that are not active theorems.
        self.context.stashExtraneousProofNotebooks()
    
    @line_magic
    def begin_common(self, line):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'common':
                raise ProveItMagicFailure("Run %begin_common in a separate notebook from %begin_%s."%self.kind)
            print "WARNING: Re-running %begin_common does not reset previously defined common expressions."
            print "         It is suggested that you restart and run all cells after editing the expressions."
        print "Defining common sub-expressions for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define common sub-expressions"
        print "%end_common will finalize the definitions"
        self.kind = 'common'

    @line_magic
    def end_common(self, line):
        # Record the context namees of common expressions referenced
        # by this context's common expressions notebook...
        self.context.recordReferencedCommons()
        # and check for illegal mutual references.
        if self.context.hasMutualReferencedCommons():
            raise ProveItMagicFailure("Not allowed to have mutually dependent 'common expression' notebooks")
        self.finish('common')

    @line_magic
    def check_expr(self, line):
        _, hash_id = os.path.split(os.path.abspath('.'))
        context = Context()
        expr_name = line.strip()
        if expr_name == '': 
            expr_name = 'expr'
            expr = self.shell.user_ns[expr_name]
        else:
            expr = self.shell.user_ns[expr_name]
            if isinstance(expr, KnownTruth):
                # actually a KnownTruth; convert to an Expression
                expr = expr.expr
        if expr != context.getStoredExpr(hash_id):
            raise ProveItMagicFailure("The built '%s' does not match the stored Expression"%expr_name)
        print "Passed sanity check: built '%s' is the same as the stored Expression."%expr_name
                                
    @line_magic
    def begin_proof(self, line):
        self.context = Context('..') # the context should be up a directory from the _proofs_ directory
        sys.path.append('..')
        theorem_name, presuming_str = str(line.strip()).split(' ', 1)
        if not presuming_str.find('presuming ') == 0:
            print "Format: %begin_proof <theorem_name> presuming [<list of theorems / context-names>]"
            return
        args = presuming_str.split(' ', 1)[-1].strip('[]').split(',')
        theorem_truth = Context('..').getTheorem(theorem_name).provenTruth
        begin_proof_result = theorem_truth.beginProof([arg.strip() for arg in args])
        print "Beginning proof of"
        if isinstance(begin_proof_result, Expression):
            # assign the theorem name to the theorem expression
            # and display this assignment
            theorem_expr = theorem_truth.expr
            self.shell.user_ns[theorem_name] = theorem_expr
            return Assignments([theorem_name], [theorem_expr], beginningProof=True)
    
    @line_magic
    def qed(self, line):
        return KnownTruth.theoremBeingProven.provenTruth.qed()

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
            context._setAxioms(self.keys, self.definitions)
        elif kind=='theorems':            
            context._setTheorems(self.keys, self.definitions)
        elif kind=='common':
            context._setCommonExpressions(self.keys, self.definitions)

        # Make an _axioms_.py or _theorems_.py file for importing axioms/theorems
        # from the certified database.
        specialStatementsClassName = kind[0].upper() + kind[1:]
        if kind=='common': specialStatementsClassName = 'CommonExpressions'        
        output = "import sys\n"
        output += "from proveit._core_.context import %s\n"%specialStatementsClassName
        output += "sys.modules[__name__] = %s(__file__)\n"%(specialStatementsClassName)        
        if os.path.isfile('_%s_.py'%kind):
            with open('_%s_.py'%kind, 'r') as f:
                if f.read() != output:
                    raise ProveItMagicFailure("An existing _%s_.py must be removed before a proper one may be autogenerated"%kind)
        else:        
            with open('_%s_.py'%kind, 'w') as f:
                f.write(output)
                
        # Reload the modules; some may reload differently after the special expression module has been written.
        # Do this before remaking the expression notebooks to make sure they are remade properly.
	'''
	for m in sys.modules.keys():
	   del(sys.modules[m]) 
	'''
	   
        # Update the expression notebooks now that these have been registered
        # as special expressions.
        for name, expr in self.definitions.iteritems():
            # remake the expression notebooks using the special expressions of the context
            context.expressionNotebook(expr)  
        
        if len(self.definitions)==0:
            print "Context %s has no %s"%(context.name, kind if kind != 'common' else 'common expressions')
        elif kind=='common':
            print "Common expressions may be imported from autogenerated _%s_.py"%kind
        else:
            print "%s may be imported from autogenerated _%s_.py"%(specialStatementsClassName, kind)
        self.ranFinish = True            

class Assignments:    
    def __init__(self, names, rightSides, beginningProof=False):
        self.beginningProof = beginningProof
        from proveit import singleOrCompositeExpression
        self.allExpressions = True
        processedRightSides = []
        for rightSide in rightSides:
            if not isinstance(rightSide, KnownTruth):
                try:
                    # try to combine a composite expression if the right side is a
                    # list or dictionary that should convert to an expression.
                    rightSide = singleOrCompositeExpression(rightSide)
                except:
                    pass
            if not isinstance(rightSide, Expression) and (rightSide is not None):
                if proveItMagic.kind is not None:
                    raise ValueError("Right hand side of end-of-cell assignment(s) is expected to be Expression(s)")
                else:
                    self.allExpressions = False
            processedRightSides.append(rightSide)
        self.names = list(names)
        self.rightSides = processedRightSides
        for name, rightSide in zip(names, rightSides):
            if rightSide is None:
                # unsetting a defintion
                proveItMagic.lowerCaseNames.remove(name.lower())
                proveItMagic.definitions.remove(name)
                proveItMagic.keys.remove(name)
                continue
            if proveItMagic.kind == 'axioms' or proveItMagic.kind == 'theorems':
                if len(rightSide.freeVars()) > 0:
                    raise ValueError('%s should not have free variables; variables must all be bound (e.g. universally quantified).'%proveItMagic.kind)
                if name in proveItMagic.definitions:
                    if proveItMagic.definitions[name] != rightSide:
                        print 'WARNING: Redefining', name
                    proveItMagic.keys.remove(name)
                elif name.lower() in proveItMagic.lowerCaseNames:
                    if not(proveItMagic.ranFinish and name in proveItMagic.definitions): # allowed to come back around after it finished once
                        raise ProveItMagicFailure("%s names must be unique regardless of capitalization"%proveItMagic.kind[:-1])
            proveItMagic.lowerCaseNames.add(name.lower())
            proveItMagic.definitions[name] = rightSide
            proveItMagic.keys.append(name)
    
    def html_line(self, name, rightSide):
        lhs_html = name
        unofficialNameKindContext = None
        if proveItMagic.kind is not None:
            kind = proveItMagic.kind
            if kind=='axioms' or kind=='theorems': kind = kind[:-1]
            unofficialNameKindContext = (name, kind, proveItMagic.context)
        rightSideStr, expr = None, None
        if isinstance(rightSide, Expression):
            expr = rightSide
            rightSideStr = rightSide._repr_html_(unofficialNameKindContext=unofficialNameKindContext)
        elif hasattr(rightSide, '_repr_html_'):
            rightSideStr = rightSide._repr_html_()
        if rightSideStr is None:
            rightSideStr = str(rightSide)
        if proveItMagic.kind == 'theorems':
            assert expr is not None, "Expecting an expression for the theorem"
            proofNotebook = proveItMagic.context.proofNotebook(name, expr)
            lhs_html = '<a href="%s" target="_blank">%s</a>'%(os.path.relpath(proofNotebook), lhs_html)
        html = '<strong id="%s">%s:</strong> %s<br>'%(name, lhs_html, rightSideStr)
        if self.beginningProof:
            expr_notebook_path = proveItMagic.context.expressionNotebook(expr)
            dependencies_notebook_path = os.path.join(os.path.split(expr_notebook_path)[0], 'dependencies.ipynb')
            html += '(see <a href="%s" target="_blank">dependencies</a>)'%(os.path.relpath(dependencies_notebook_path))
        return html

    def _repr_html_(self):
        return '\n'.join(self.html_line(name, rightSide) for name, rightSide in zip(self.names, self.rightSides))
        
    def __repr__(self):
        return '\n'.join('%s: %s'%(name, repr(rightSide)) for name, rightSide in zip(self.names, self.rightSides))
        

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
