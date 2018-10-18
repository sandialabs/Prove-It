'''
Define some custom magic for Prove-It in IPython notebooks.
'''

from IPython.core.magic import Magics, magics_class, line_magic
from IPython import get_ipython
from IPython.display import display, HTML
import nbformat
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
            non_indented_line_indices = [k for k, line in enumerate(lines) if len(line) > 0 and re.match("\s", line[0]) is None]
            if len(non_indented_line_indices)==0: 
                # no non-indented lines.  just run the cell normally.
                new_raw_cell = '\n'.join(lines)
                return ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
            # get the last non-indented line and all indented lines that follow
            last_python_stmt = '\n'.join(lines[non_indented_line_indices[-1]:])
            # look for one or more variables on the left side of an assignment
            if re.match("[a-zA-Z_][a-zA-Z0-9_\.]*\s*(,\s*[a-zA-Z_][a-zA-Z0-9_\.]*)*\s*=", last_python_stmt) is not None:
                lhs, rhs = last_python_stmt.split('=', 1)
                lhs = lhs.strip(); rhs = rhs.strip()
                if lhs != 'context' and rhs.find("proveit.Context('.')") != 0:
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

class ContextInterface:
    '''
    A SubContexts object is an interface for the _sub_contexts_.txt file
    which stores the names of the sub-contexts of the context in the current
    directory and also tracks whether it is in interactive or state mode.
    With each %context execution (in the _context_.ipynb notebook), the
    mode is toggled.  If in interactive mode, the SUbContexts object is
    responsible for creating the interactive widget to add/modify/remove
    sub-contexts and edit their brief descriptions.
    '''
    def __init__(self):
        self.context = Context() # context of the current working directory
        self.subContextNames = list(self.context.getSubContextNames())
        self.subContextDescriptions = dict()
        
        # read the previous 'mode' (interactive or static) and toggle it.
        prev_mode = 'static' # default toggles 'static' to 'interactive'
        if os.path.isfile('_mode_.txt'):
            with open('_mode_.txt', 'rt') as f:
                prev_mode = f.read().strip()
        # mode toggles between 'static' and 'interactive'
        if prev_mode == 'static':
            self.mode = 'interactive'
            # in interactive mode, sub-contexts are presented in an interactive widget
            self.widget = widgets.VBox()
            self.smallButtonLayout = widgets.Layout(width='30px')
            self.subContextLinkLayout = widgets.Layout(width='20%')
            self.subContextDescriptionLayout = widgets.Layout(width='80%')
        else:
            self.mode = 'static'
        
        # write the new mode that has been toggled
        with open('_mode_.txt', 'w') as f:
            f.write(self.mode + '\n')
        
        # register each sub-context name, reading their brief descriptions and
        # creating widgets if in interactive mode
        for sub_context_name in self.subContextNames:
            self._addSubContextRow(sub_context_name)
    
    def _addSubContextRow(self, subContextName):
        subContextDescription = self.readDescription(subContextName)
        self.subContextDescriptions[subContextName] = subContextDescription
        if self.mode == 'interactive':
            small_button_layout = self.smallButtonLayout
            sub_context_link_layout = self.subContextLinkLayout
            sub_context_description_layout = self.subContextDescriptionLayout
            #rename_button =  widgets.Button(description='', disabled=False, button_style='', tooltip='rename', icon='pencil', layout=small_button_layout)
            up_button = widgets.Button(description='', disabled=False, button_style='', tooltip='move up', icon='chevron-up', layout=small_button_layout)
            dn_button = widgets.Button(description='', disabled=False, button_style='', tooltip='move down', icon='chevron-down', layout=small_button_layout)
            delete_button = widgets.Button(description='', disabled=False, button_style='danger', tooltip='delete context', icon='trash', layout=small_button_layout)
            href = self.subContextNotebook(subContextName)
            sub_context_link = widgets.HTML('<a class="ProveItLink" href="%s">%s</a>'%(href,subContextName) , layout=sub_context_link_layout)
            sub_context_description = widgets.Text(value=subContextDescription, placeholder='Add a brief description here...', layout=sub_context_description_layout)
            def setDescription(change):
                self.subContextDescriptions[subContextName] = change['new']
                self.writeDescriptionFile(subContextName)
            sub_context_description.observe(setDescription, names='value')
            row_widget = widgets.VBox([widgets.HBox([sub_context_link, sub_context_description, up_button, dn_button, delete_button])])
            self.widget.children = self.widget.children + (row_widget,)
            def moveUp(sender):
                idx = self.subContextNames.index(subContextName)
                self.moveUp(idx)
            def moveDown(sender):
                idx = self.subContextNames.index(subContextName)
                self.moveUp(idx+1)
            def deleteSubContext(sender):
                # before deleting a sub-context, we need confirmation by entering the sub-context name
                delete_msg = widgets.Label("To remove (unlink) sub-context, enter its name as confirmation", layout={'width':'400px', 'max_width':'400px'})
                verification_text = widgets.Text(layout=widgets.Layout(flex_grow=2, max_width='500px'))
                cancel_button = widgets.Button(description='cancel', disabled=False, tooltip='cancel', layout={'width':'80px'})
                cancel_button.on_click(dismissDelete)
                verification_text.observe(monitorConfirmation)
                row_widget.children = (row_widget.children[0], widgets.HBox([delete_msg, verification_text, cancel_button], layout={'justify_content':'flex-end'}))
            def dismissDelete(sender):
                # dismiss the delete confirmation/message by removing all be the first row in the row_widget
                row_widget.children = (row_widget.children[0],)
            def monitorConfirmation(change):
                # check to see if the user has entered the sub-context name for confirmation
                if change['new'] == subContextName:
                    # delete context has been 
                    self.deleteSubContext(subContextName)
            up_button.on_click(moveUp)
            dn_button.on_click(moveDown)
            delete_button.on_click(deleteSubContext)
    
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
            super_context_links = Context('.').links(from_directory=subContextName)
            nb = nb.replace('#CONTEXT#', super_context_links + '.' + subContextName)
        # write the notebook file
        with open(notebook_name, 'w') as notebook_file:
            notebook_file.write(nb)
        return notebook_name        
    
    def addSubContext(self, subContextName):
        '''
        Add a new sub-context with the given name.
        '''
        if subContextName in self.subContextNames:
            return
        if subContextName=='': return
        self.context.appendSubContextName(subContextName)
        self.subContextNames.append(subContextName)
        self._addSubContextRow(subContextName)
    
    def deleteSubContext(self, contextNameToDelete):
        '''
        Delete (unlink) a sub-context with the given name as long as there are not external
        references to its expressions.  Either way, the directory will remain.
        Only files in the __pv_it directories are cleared (recursively in all sub-sub contexts,
        etc) and the current directory's context will no longer link to it.  That is
        why we use the term 'unlinked'.  It may be resurrected by adding the sub-context
        with the same name back in.
        '''
        context = Context(contextNameToDelete)
        # remove all internal references and see if any external references remain
        context.clearAll() 
        contains_expressions = context.containsAnyExpression()
        def dismiss(sender):
            if not contains_expressions:
                # Successful removal; we need to remove the deleted sub-context name from
                # the self.subContextNames list, the displayed widgets, and the list in _sub_contexts_.txt.
                new_sub_contexts = []
                new_widget_children = []
                for k, sub_context_name in enumerate(self.subContextNames):
                    if sub_context_name != contextNameToDelete:
                        new_sub_contexts.append(sub_context_name)
                        new_widget_children.append(self.widget.children[k])
                self.subContextNames = new_sub_contexts
                self.updateSubContextNames()
                self.widget.children = new_widget_children
            else:
                # dismiss the delete confirmation/message by removing all but the first row in the row_widget
                row_widget.children = (row_widget.children[0],)
        if not contains_expressions:
            msg = 'Removing (unlinking) sub-context; add it again to resurrect it or delete the directory to make it permanent'
            msg_width = '650px'
        else:
            msg = "Context removal cancelled; there are external references to its expressions (or corrupted '__pv_it' directories)"
            msg_width = '650px'
        row_widget = self.widget.children[self.subContextNames.index(contextNameToDelete)]
        delete_msg = widgets.Label(msg, layout={'width':msg_width, 'max_width':msg_width})
        gotit_button = widgets.Button(description='got it', disabled=False, tooltip='got it', layout={'width':'80px'})
        gotit_button.on_click(dismiss)
        row_widget.children = (row_widget.children[0], widgets.HBox([delete_msg, gotit_button], layout=widgets.Layout(justify_content='flex-end')))
    
    def moveUp(self, i):
        if i<=0 or i==len(self.widget.children): return # can't move the first entry up or go beyond the last entry
        self.widget.children = self.widget.children[:i-1] + (self.widget.children[i], self.widget.children[i-1]) + self.widget.children[i+1:]
        self.subContextNames = self.subContextNames[:i-1] + [self.subContextNames[i], self.subContextNames[i-1]] + self.subContextNames[i+1:]
        self.updateSubContextNames()

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

    def updateSubContextNames(self):
        '''
        Update the stored sub-context names (in the _sub_contexts_.txt file) with
        self.subContextNames
        '''
        # rewrite the sub_contexts.txt file with new information.
        self.context.setSubContextNames(self.subContextNames)

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
        # create an '_init_.py' in the directory if there is not an existing one.
        if not os.path.isfile('__init__.py'):
            open('__init__.py', 'w').close() # create an empty __init__.py
        context = Context()
        proveit_path = os.path.split(proveit.__file__)[0]
        special_notebook_types = ('common', 'axioms', 'theorems', 'demonstrations')
        special_notebook_texts = ('common expressions', 'axioms', 'theorems', 'demonstrations')
        for special_notebook_type in special_notebook_types:
            notebook_name = '_%s_.ipynb'%special_notebook_type
            if not os.path.isfile(notebook_name):
                # notebook does not yet exist, create it from the template
                template_name = '_%s_template_.ipynb'%special_notebook_type
                with open(os.path.join(proveit_path, '..', template_name), 'r') as template:
                    nb = template.read()
                    nb = nb.replace('#CONTEXT#', context.name)
                # write the notebook file
                with open(notebook_name, 'w') as notebook_file:
                    notebook_file.write(nb)
                    
        context_interface = ContextInterface()
        
        if context_interface.mode == 'static':
            special_notebooks_html = '<table>\n'
            for special_notebook_type, special_notebook_text in zip(special_notebook_types, special_notebook_texts):
                special_notebooks_html += '<th><a class="ProveItLink" href="_%s_.ipynb">%s</a></th>\n'%(special_notebook_type, special_notebook_text)
            special_notebooks_html += '</table>\n'
            if len(context_interface.subContextNames) > 0:
                special_notebooks_html += '<table>\n'
                for name in context_interface.subContextNames:
                    description = context_interface.subContextDescriptions[name]
                    href = context_interface.subContextNotebook(name)
                    special_notebooks_html += '<tr><th><a class="ProveItLink" href="%s">%s</a></th><td>%s</td></tr>\n'%(href, name, description)
                special_notebooks_html += '</table>\n'                
            display(HTML(special_notebooks_html))
        else:
            special_notebook_links = []
            full_width_layout = widgets.Layout(width='100%', padding='5px')
            for special_notebook_type, special_notebook_text in zip(special_notebook_types, special_notebook_texts):
                special_notebook_links.append(widgets.HTML('<a class="ProveItLink" href="_%s_.ipynb">%s</a>'%(special_notebook_type, special_notebook_text), layout=full_width_layout))
            special_notebook_links = widgets.HBox(special_notebook_links)
                
            sub_contexts_label = widgets.Label('List of sub-contexts:', layout = widgets.Layout(width='100%'))
            #sub_context_widgets = widgets.VBox(sub_context_widgets)
            add_context_widget = widgets.Text(value='', placeholder='Add sub-context...')
            def addSubContext(sender):
                context_interface.addSubContext(add_context_widget.value)
                add_context_widget.value = ''
            add_context_widget.on_submit(addSubContext)
            #layout = widgets.Layout(display='flex', flex_flow='column-reverse')
            #display(widgets.Button(description='Edit...', disabled=False, button_style='', tooltip='Edit the sub-contents list', layout=layout))
            #layout = widgets.Layout(float='bottom')
            display(widgets.VBox([special_notebook_links, sub_contexts_label, context_interface.widget, add_context_widget]))       
    
    def begin_axioms(self):
        # context based upon current working directory
        self.context = Context()
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'axioms':
                raise ProveItMagicFailure("Run %%begin_axioms in a separate notebook from %%begin_%s."%self.kind)
            print "WARNING: Re-running %begin_axioms does not reset previously defined axioms."
            print "         It is suggested that you restart and run all cells after editing axioms."
        print "Defining axioms for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define axioms"
        print "%end_axioms will finalize the definitions"

    def end_axioms(self):
        self._finish('axioms')

    def begin_theorems(self):
        # context based upon current working directory
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'theorems':
                raise ProveItMagicFailure("Run %%begin_theorems in a separate notebook from %%begin_%s."%self.kind)
            print "WARNING: Re-running %begin_theorems does not reset previously defined theorems."
            print "         It is suggested that you restart and run all cells after editing theorems."
        print "Defining theorems for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define theorems"
        print "'%end theorems' will finalize the definitions"

    def end_theorems(self):
        self._finish('theorems')
        # stash proof notebooks that are not active theorems.
        self.context.stashExtraneousProofNotebooks()
    
    def begin_common(self):
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'common':
                raise ProveItMagicFailure("Run '%%begin common' in a separate notebook from %%begin_%s."%self.kind)
            print "WARNING: Re-running '%begin common' does not reset previously defined common expressions."
            print "         It is suggested that you restart and run all cells after editing the expressions."
        print "Defining common sub-expressions for context '" + self.context.name + "'"
        print "Subsequent end-of-cell assignments will define common sub-expressions"
        print "%end_common will finalize the definitions"

    def end_common(self):
        # Record the context names of common expressions referenced
        # by this context's common expressions notebook...
        self.context.recordCommonExprDependencies()
        # and check for illegal mutual references.
        cyclically_referenced_common_expr_context = self.context.cyclicallyReferencedCommonExprContext()
        if cyclically_referenced_common_expr_context is not None:
            raise ProveItMagicFailure("Not allowed to have cyclically dependent 'common expression' notebooks: %s._common_"%cyclically_referenced_common_expr_context)
        self._finish('common')
    
    @line_magic
    def begin(self, line):
        kind = line.strip()
        # context based upon current working directory
        self.context = Context()        
        if kind == 'axioms':
            self.begin_axioms()
        elif kind == 'theorems':
            self.begin_theorems()
        elif kind == 'common':
            self.begin_common()
        self.kind = kind

    @line_magic
    def end(self, line):
        kind = line.strip()
        if kind == 'axioms':
            self.end_axioms()
        elif kind == 'theorems':
            self.end_theorems()
        elif kind == 'common':
            self.end_common()
        # reference any expressions that were displayed:
        self.context.referenceDisplayedExpressions(kind)
        # clean unreferenced expressions:
        self.context.clean()
        self.kind = None

    @line_magic
    def clear(self, line):
        kind = line.strip()
        # context based upon current working directory
        self.context = Context()        
        if kind == 'axioms':
            self.context._clearAxioms()
        elif kind == 'theorems':
            self.context._clearTheorems()
        elif kind == 'common':
            self.context._clearCommonExressions()
        elif KnownTruth.theoremBeingProven is not None:
            kind = '_proof_' + KnownTruth.theoremBeingProven.name
        # clean unreferenced expressions:
        self.context.referenceDisplayedExpressions(kind, clear=True)
        self.context.clean()
        self.kind = None
                
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
        stored_expr = context.getStoredExpr(hash_id)
        if expr != stored_expr:
            raise ProveItMagicFailure("The built '%s' does not match the stored Expression"%expr_name)
        if expr._style_id != stored_expr._style_id:
            raise ProveItMagicFailure("The built '%s' style does not match that of the stored Expression"%expr_name)
        print "Passed sanity check: built '%s' is the same as the stored Expression."%expr_name
                                
    @line_magic
    def proving(self, line):
        from proveit._core_.proof import Theorem
        self.context = Context('..') # the context should be up a directory from the _proofs_ directory
        sys.path.append('..')
        theorem_name, presuming_str = str(line.strip()).split(' ', 1)
        if not presuming_str.find('presuming ') == 0:
            print "Format: %begin_proof <theorem_name> presuming [<list of theorems / context-names>]"
            return
        args = presuming_str.split(' ', 1)[-1].strip('[]').split(',')
        theorem_truth = Context('..').getTheorem(theorem_name).provenTruth
        print "Beginning proof of", theorem_name
        presuming = [arg.strip() for arg in args if arg.strip() != '']
        # The list of theorems/context-names may be composed of full-path strings containing '.'s
        # or may be actual theorem variables defined in the IPython sesson.  The latter
        # instances will be converted to strings.
        for k, arg in enumerate(list(presuming)):
            if '.' not in arg:
                knownTruth = self.shell.user_ns[arg]
                if not isinstance(knownTruth, KnownTruth) or not isinstance(knownTruth.proof(), Theorem):
                    raise ValueError("Presuming list must be composed of full-path theorem/context-name containing '.'s or be KnownTruth variable representing a Theorem")
                theorem = knownTruth.proof()
                presuming[k] = str(theorem) # full path of theorem 
        begin_proof_result = theorem_truth.beginProof(presuming)
        if isinstance(begin_proof_result, Expression):
            # assign the theorem name to the theorem expression
            # and display this assignment
            theorem_expr = theorem_truth.expr
            self.shell.user_ns[theorem_name] = theorem_expr
            return Assignments([theorem_name], [theorem_expr], beginningProof=True)
    
    @line_magic
    def qed(self, line):
        proof = KnownTruth.theoremBeingProven.provenTruth._qed()
        proof._repr_html_() # generate expressions that should be referenced
        self.context.referenceDisplayedExpressions('_proof_' + KnownTruth.theoremBeingProven.name)
        # clean unreferenced expressions:
        self.context.clean()
        return proof

    def _finish(self, kind):
        '''
        Finish 'axioms', 'theorems', or 'common' for the Context
        associated with the current working directory.
        '''
        if self.kind != kind:
            raise ProveItMagicFailure(r"Must run %begin " + kind + r" before %end " + kind)
        # Add the special statements / expressions to the context
        context = self.context
        if kind=='axioms':
            context._setAxioms(self.keys, self.definitions)
        elif kind=='theorems':            
            context._setTheorems(self.keys, self.definitions)
        elif kind=='common':
            context._setCommonExpressions(self.keys, self.definitions)
        
        # Make a _common_.py, _axioms_.py or _theorems_.py for importing
        # expressions from the certified database.
        context.makeSpecialExprModule(kind)
	   
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
            print "%s may be imported from autogenerated _%s_.py"%((kind[0].upper() + kind[1:]), kind)
        self.ranFinish = True       
    
    @line_magic
    def dependencies(self, line):
        '''
        Show the dependencies of an axiom or theorem.
        '''
        from .proof import Theorem
        name = line.strip()
        known_truth = self.shell.user_ns[line.strip()]
        proof = known_truth.proof() # Axiom or Theorem
        
        def displaySpecialStmt(stmt):
            '''
            Given an Axiom or Theorem, display HTML with a link
            to the definition.
            '''
            expr = stmt.provenTruth.expr
            display(HTML('<dt><a class="ProveItLink" href="%s">%s</a></dt><dd>%s</dd>'%(stmt.getLink(), str(stmt), expr._repr_html_())))
        
        def stmt_sort(stmt):
            return str(stmt)
        
        if isinstance(proof, Theorem):
            try:
                required_axioms, required_unproven_theorems = proof.allRequirements()
            except:
                display(HTML('<h3>This theorem has not been proven yet.</h3>'))
                required_axioms, required_unproven_theorems = tuple(), tuple()
                
            if len(required_unproven_theorems) > 0:
                display(HTML('<h3>Unproven theorems required (directly or indirectly) to prove %s</h3>'%name))
                display(HTML('<dl>'))
                for required_unproven_theorem in sorted(required_unproven_theorems, key=stmt_sort):
                    displaySpecialStmt(Context.findTheorem(required_unproven_theorem))
                display(HTML('</dl>'))
            if len(required_axioms) > 0:
                display(HTML('<h3>Axioms required (directly or indirectly) to prove %s</h3>'%name))
                display(HTML('<dl>'))
                for required_axiom in sorted(required_axioms, key=stmt_sort):       
                    displaySpecialStmt(Context.findAxiom(required_axiom))
                display(HTML('</dl>'))
        
        dependents = proof.directDependents()
        if len(dependents) == 0:
            display(HTML('<h3>No theorems depend upon %s</h3>'%name))
        else:
            display(HTML('<h3>Theorems that depend directly on %s</h3>'%name))
            display(HTML('<dl>'))
            for dependent in sorted(proof.directDependents(), key=stmt_sort):
                displaySpecialStmt(Context.findTheorem(dependent))
            display(HTML('</dl>'))

class Assignments:    
    def __init__(self, names, rightSides, beginningProof=False):
        self.beginningProof = beginningProof
        from proveit import singleOrCompositeExpression
        processedRightSides = []
        for rightSide in rightSides:
            if not isinstance(rightSide, KnownTruth):
                try:
                    # try to combine a composite expression if the right side is a
                    # list or dictionary that should convert to an expression.
                    rightSide = singleOrCompositeExpression(rightSide)
                except:
                    pass
            if proveItMagic.kind in ('axioms', 'theorems', 'common'):
                if not isinstance(rightSide, Expression) and (rightSide is not None):
                    raise ValueError("Right hand side of end-of-cell assignment(s) is expected to be Expression(s)")
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
                    raise ValueError('%s should not have free variables; variables must all be bound (e.g. universally quantified).  Free variables: %s'%(proveItMagic.kind, rightSide.freeVars()))
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
        if proveItMagic.kind in ('axioms', 'theorems', 'common'):
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
            lhs_html = '<a class="ProveItLink" href="%s">%s</a>'%(os.path.relpath(proofNotebook), lhs_html)
        html = '<strong id="%s">%s:</strong> %s<br>'%(name, lhs_html, rightSideStr)
        if self.beginningProof:
            expr_notebook_path = proveItMagic.context.expressionNotebook(expr)
            dependencies_notebook_path = os.path.join(os.path.split(expr_notebook_path)[0], 'dependencies.ipynb')
            html += '(see <a class="ProveItLink" href="%s">dependencies</a>)'%(os.path.relpath(dependencies_notebook_path))
        return html

    def _repr_html_(self):
        if len(self.names) == 0: return
        try:
            return '\n'.join(self.html_line(name, rightSide) for name, rightSide in zip(self.names, self.rightSides))
        except Exception as e:
            print e
        
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
