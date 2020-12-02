'''
Define some custom magic for Prove-It in IPython notebooks.
'''

from IPython.core.magic import Magics, magics_class, line_magic
from IPython import get_ipython
from IPython.display import display, HTML
from proveit._core_.expression import Expression, free_vars
from proveit._core_ import Judgment, Theorem
from proveit._core_.theory import Theory
import ipywidgets as widgets
#import new#Comment out for python 3
import types#Added for python 3
import re
import os
import sys
#from ._theory_storage import relurl#Comment out for Python 3
from proveit._core_._theory_storage import relurl#Comment in for Python 3

class AssignmentBehaviorModifier:
    def __init__(self):
        self.ipython = ipython = get_ipython()
        # prevent unwanted overwriting when the extension is reloaded
        if not hasattr(ipython, 'orig_run_cell'):
            # remember the original version of 'run_cell'
            ipython.orig_run_cell = ipython.run_cell
    
    def _setBehavior(self, assignmentFn, lastLineFn):
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
                if len(rhs)>0 and rhs[0] != '=': # "==" doesn't count
                    lhs = lhs.strip(); rhs = rhs.strip()
                    if lhs != 'theory' and rhs.find("proveit.Theory('.')") != 0:
                        lines.append(assignmentFn([varname.strip() for varname in lhs.split(',') ]))
            elif re.match("[a-zA-Z_][a-zA-Z0-9_\.]*$", last_python_stmt) is not None:
                # We may alter the last line for dispaly purposes.
                lines.append(lastLineFn(last_python_stmt))
            new_raw_cell = '\n'.join(lines)
            return ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
#        ipython.run_cell = new.instancemethod(new_run_cell, ipython)#Comment out for python 3
        ipython.run_cell = types.MethodType(new_run_cell, ipython)#Add for python 3
    
    def resetBehavior(self):
        ipython = self.ipython
        ipython.run_cell = ipython.orig_run_cell

    def displayAssignments(self, shell):
#        shell.ex("from proveit._core_.magics import Assignments")#Comment out for Python 3
        shell.ex("import proveit.magics")#Comment in for Python 3
        self._setBehavior(lambda varnames: "proveit.magics.Assignments([" + ','.join("'%s'"%varname for varname in varnames) + "], [" + ','.join(varnames) + "])",
                          lambda orig_last_line: "proveit.magics.possibly_wrap_html_display_objects(%s)"%orig_last_line)

class TheoryInterface:
    '''
    A SubTheories object is an interface for the _sub_theories_.txt file
    which stores the names of the sub-theories of the theory in the current
    directory and also tracks whether it is in interactive or state mode.
    With each %theory execution (in the _theory_.ipynb notebook), the
    mode is toggled.  If in interactive mode, the SubTheories object is
    responsible for creating the interactive widget to add/modify/remove
    sub-theories and edit their brief descriptions.
    '''
    def __init__(self):
        self.theory = Theory() # theory of the current working directory
        self.subTheoryNames = list(self.theory.getSubTheoryNames())
        self.subTheoryDescriptions = dict()
        
        # read the previous 'mode' (interactive or static) and toggle it.
        prev_mode = 'static' # default toggles 'static' to 'interactive'
        if os.path.isfile('_mode_.txt'):
            with open('_mode_.txt', 'rt') as f:
                prev_mode = f.read().strip()
        # mode toggles between 'static' and 'interactive'
        if prev_mode == 'static':
            self.mode = 'interactive'
            # in interactive mode, sub-theories are presented in an interactive widget
            self.widget = widgets.VBox()
            self.smallButtonLayout = widgets.Layout(width='30px')
            self.subTheoryLinkLayout = widgets.Layout(width='20%')
            self.subTheoryDescriptionLayout = widgets.Layout(width='80%')
        else:
            self.mode = 'static'
        
        # write the new mode that has been toggled
        with open('_mode_.txt', 'w') as f:
            f.write(self.mode + '\n')
        
        # register each sub-theory name, reading their brief descriptions and
        # creating widgets if in interactive mode
        for sub_theory_name in self.subTheoryNames:
            self._addSubTheoryRow(sub_theory_name)
    
    def _addSubTheoryRow(self, subTheoryName):
        subTheoryDescription = self.readDescription(subTheoryName)
        self.subTheoryDescriptions[subTheoryName] = subTheoryDescription
        if self.mode == 'interactive':
            small_button_layout = self.smallButtonLayout
            sub_theory_link_layout = self.subTheoryLinkLayout
            sub_theory_description_layout = self.subTheoryDescriptionLayout
            #rename_button =  widgets.Button(description='', disabled=False, button_style='', tooltip='rename', icon='pencil', layout=small_button_layout)
            up_button = widgets.Button(description='', disabled=False, button_style='', tooltip='move up', icon='chevron-up', layout=small_button_layout)
            dn_button = widgets.Button(description='', disabled=False, button_style='', tooltip='move down', icon='chevron-down', layout=small_button_layout)
            delete_button = widgets.Button(description='', disabled=False, button_style='danger', tooltip='delete theory', icon='trash', layout=small_button_layout)
            href = self.subTheoryNotebook(subTheoryName)
            sub_theory_link = widgets.HTML('<a class="ProveItLink" href="%s">%s</a>'%(href,subTheoryName) , layout=sub_theory_link_layout)
            sub_theory_description = widgets.Text(value=subTheoryDescription, placeholder='Add a brief description here...', layout=sub_theory_description_layout)
            def setDescription(change):
                self.subTheoryDescriptions[subTheoryName] = change['new']
                self.writeDescriptionFile(subTheoryName)
            sub_theory_description.observe(setDescription, names='value')
            row_widget = widgets.VBox([widgets.HBox([sub_theory_link, sub_theory_description, up_button, dn_button, delete_button])])
            self.widget.children = self.widget.children + (row_widget,)
            def moveUp(sender):
                idx = self.subTheoryNames.index(subTheoryName)
                self.moveUp(idx)
            def moveDown(sender):
                idx = self.subTheoryNames.index(subTheoryName)
                self.moveUp(idx+1)
            def deleteSubTheory(sender):
                # before deleting a sub-theory, we need confirmation by entering the sub-theory name
                delete_msg = widgets.Label("To remove (unlink) sub-theory, enter its name as confirmation", layout={'width':'400px', 'max_width':'400px'})
                verification_text = widgets.Text(layout=widgets.Layout(flex_grow=2, max_width='500px'))
                cancel_button = widgets.Button(description='cancel', disabled=False, tooltip='cancel', layout={'width':'80px'})
                cancel_button.on_click(dismissDelete)
                verification_text.observe(monitorConfirmation)
                row_widget.children = (row_widget.children[0], widgets.HBox([delete_msg, verification_text, cancel_button], layout={'justify_content':'flex-end'}))
            def dismissDelete(sender):
                # dismiss the delete confirmation/message by removing all be the first row in the row_widget
                row_widget.children = (row_widget.children[0],)
            def monitorConfirmation(change):
                # check to see if the user has entered the sub-theory name for confirmation
                if change['new'] == subTheoryName:
                    # delete theory has been 
                    self.deleteSubTheory(subTheoryName)
            up_button.on_click(moveUp)
            dn_button.on_click(moveDown)
            delete_button.on_click(deleteSubTheory)
    
    def subTheoryNotebook(self, subTheoryName):
        '''
        Returns the path of the _theory_.ipynb notebook for the given sub-theory,
        creating it if necessary.
        '''
        import proveit
        notebook_name = os.path.join(subTheoryName, '_theory_.ipynb')
        if not os.path.isdir(subTheoryName):
            os.mkdir(subTheoryName)
            init_name = os.path.join(subTheoryName, '__init__.py')
            open(init_name, 'w')
        if os.path.isfile(notebook_name):
            # already exists
            return notebook_name
        proveit_path = os.path.split(proveit.__file__)[0]
        with open(os.path.join(proveit_path, '..', '_theory_template_.ipynb'), 'r') as template:
            nb = template.read()
            super_theory_links = Theory('.').links(from_directory=subTheoryName)
            nb = nb.replace('#THEORY#', super_theory_links + '.' + subTheoryName)
        # write the notebook file
        with open(notebook_name, 'w') as notebook_file:
            notebook_file.write(nb)
        return notebook_name        
    
    def addSubTheory(self, subTheoryName):
        '''
        Add a new sub-theory with the given name.
        '''
        if subTheoryName in self.subTheoryNames:
            return
        if subTheoryName=='': return
        self.theory.appendSubTheoryName(subTheoryName)
        self.subTheoryNames.append(subTheoryName)
        self._addSubTheoryRow(subTheoryName)
    
    def deleteSubTheory(self, theoryNameToDelete):
        '''
        Delete (unlink) a sub-theory with the given name as long as there are not external
        references to its expressions.  Either way, the directory will remain.
        Only files in the __pv_it directories are cleared (recursively in all sub-sub theories,
        etc) and the current directory's theory will no longer link to it.  That is
        why we use the term 'unlinked'.  It may be resurrected by adding the sub-theory
        with the same name back in.
        '''
        theory = Theory(theoryNameToDelete)
        # remove all internal references and see if any external references remain
        theory.clearAll() 
        contains_expressions = theory.containsAnyExpression()
        def dismiss(sender):
            if not contains_expressions:
                # Successful removal; we need to remove the deleted sub-theory name from
                # the self.subTheoryNames list, the displayed widgets, and the list in _sub_theories_.txt.
                new_sub_theories = []
                new_widget_children = []
                for k, sub_theory_name in enumerate(self.subTheoryNames):
                    if sub_theory_name != theoryNameToDelete:
                        new_sub_theories.append(sub_theory_name)
                        new_widget_children.append(self.widget.children[k])
                self.subTheoryNames = new_sub_theories
                self.updateSubTheoryNames()
                self.widget.children = new_widget_children
            else:
                # dismiss the delete confirmation/message by removing all but the first row in the row_widget
                row_widget.children = (row_widget.children[0],)
        if not contains_expressions:
            msg = 'Removing (unlinking) sub-theory; add it again to resurrect it or delete the directory to make it permanent'
            msg_width = '650px'
        else:
            msg = "Theory removal cancelled; there are external references to its expressions (or corrupted '__pv_it' directories)"
            msg_width = '650px'
        row_widget = self.widget.children[self.subTheoryNames.index(theoryNameToDelete)]
        delete_msg = widgets.Label(msg, layout={'width':msg_width, 'max_width':msg_width})
        gotit_button = widgets.Button(description='got it', disabled=False, tooltip='got it', layout={'width':'80px'})
        gotit_button.on_click(dismiss)
        row_widget.children = (row_widget.children[0], widgets.HBox([delete_msg, gotit_button], layout=widgets.Layout(justify_content='flex-end')))
    
    def moveUp(self, i):
        if i<=0 or i==len(self.widget.children): return # can't move the first entry up or go beyond the last entry
        self.widget.children = self.widget.children[:i-1] + (self.widget.children[i], self.widget.children[i-1]) + self.widget.children[i+1:]
        self.subTheoryNames = self.subTheoryNames[:i-1] + [self.subTheoryNames[i], self.subTheoryNames[i-1]] + self.subTheoryNames[i+1:]
        self.updateSubTheoryNames()

    def readDescription(self, subTheoryName):
        brief_description = ''
        brief_description_filename = os.path.join(subTheoryName, '_brief_description_.txt')
        if os.path.isfile(brief_description_filename):
            with open(brief_description_filename) as f2:
                brief_description = f2.read().strip()
        self.subTheoryDescriptions[subTheoryName] = brief_description
        return brief_description

    def writeDescriptionFile(self, subTheoryName):
        brief_description = self.subTheoryDescriptions[subTheoryName]
        if brief_description != '':
            brief_description_filename = os.path.join(subTheoryName, '_brief_description_.txt')
            with open(brief_description_filename, 'w') as f:
                f.write(brief_description + '\n')

    def updateSubTheoryNames(self):
        '''
        Update the stored sub-theory names (in the _sub_theories_.txt file) with
        self.subTheoryNames
        '''
        # rewrite the sub_theories.txt file with new information.
        self.theory.setSubTheoryNames(self.subTheoryNames)

class ProveItMagicCommands:
    def __init__(self):
        self.reset()
    
    def reset(self):
        # You must call the parent constructor
        self.kind = None
        self.definitions = dict() # map name to expression
        self.expr_names = dict() # map expression to names
        self.keys = [] # the keys of the definitions in the order they appear
        self.lowerCaseNames = set()
        self.theory = None 
        self.ranFinish = False    
    
    def display_contents(self, theory_names):
        '''
        Generates a "table of contents" hierarchy of theories for the theories
        listed in the line.
        '''
        def generateContents(theories):
            if len(theories)==0: return ''
            html = '<ul>\n'        
            for theory in theories:
                href = relurl(os.path.join(theory.getPath(), '_theory_.ipynb'))
                html += '<li><a class="ProveItLink" href="%s">%s</a></li>\n'%(href, theory.name)
                html += generateContents(list(theory.getSubTheories()))
            return html + '</ul>\n'
        display(HTML(generateContents([Theory(theory_name) for theory_name in theory_names])))
            
    def display_theory(self):
        '''
        Create the _common_, _axioms_ and _theorems_ notebooks for the current
        theory (if they do not already exist).  Show the table of contents
        for sub-theories which may be edited.
        '''
        import proveit
        # create an '__init__.py' in the directory if there is not an existing one.
        if not os.path.isfile('__init__.py'):
            open('__init__.py', 'w').close() # create an empty __init__.py
        theory = Theory()
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
                    nb = nb.replace('#THEORY#', theory.name)
                # write the notebook file
                with open(notebook_name, 'w') as notebook_file:
                    notebook_file.write(nb)
                    
        theory_interface = TheoryInterface()
        
        if theory_interface.mode == 'static':
            special_notebooks_html = '<table><tr>\n'
            for special_notebook_type, special_notebook_text in zip(special_notebook_types, special_notebook_texts):
                special_notebooks_html += '<th><a class="ProveItLink" href="_%s_.ipynb">%s</a></th>\n'%(special_notebook_type, special_notebook_text)
            special_notebooks_html += '</tr></table>\n'
            if len(theory_interface.subTheoryNames) > 0:
                special_notebooks_html += '<table>\n'
                for name in theory_interface.subTheoryNames:
                    description = theory_interface.subTheoryDescriptions[name]
                    href = theory_interface.subTheoryNotebook(name)
                    special_notebooks_html += '<tr><th><a class="ProveItLink" href="%s">%s</a></th><td>%s</td></tr>\n'%(href, name, description)
                special_notebooks_html += '</table>\n'                
            display(HTML(special_notebooks_html))
        else:
            special_notebook_links = []
            full_width_layout = widgets.Layout(width='100%', padding='5px')
            for special_notebook_type, special_notebook_text in zip(special_notebook_types, special_notebook_texts):
                special_notebook_links.append(widgets.HTML('<a class="ProveItLink" href="_%s_.ipynb">%s</a>'%(special_notebook_type, special_notebook_text), layout=full_width_layout))
            special_notebook_links = widgets.HBox(special_notebook_links)
                
            sub_theories_label = widgets.Label('List of sub-theories:', layout = widgets.Layout(width='100%'))
            #sub_theory_widgets = widgets.VBox(sub_theory_widgets)
            add_theory_widget = widgets.Text(value='', placeholder='Add sub-theory...')
            def addSubTheory(sender):
                theory_interface.addSubTheory(add_theory_widget.value)
                add_theory_widget.value = ''
            add_theory_widget.on_submit(addSubTheory)
            #layout = widgets.Layout(display='flex', flex_flow='column-reverse')
            #display(widgets.Button(description='Edit...', disabled=False, button_style='', tooltip='Edit the sub-contents list', layout=layout))
            #layout = widgets.Layout(float='bottom')
            display(widgets.VBox([special_notebook_links, sub_theories_label, theory_interface.widget, add_theory_widget]))       
    
    def begin_axioms(self):
        # theory based upon current working directory
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'axioms':
                raise ProveItMagicFailure("Run %%begin_axioms in a separate notebook from %%begin_%s."%self.kind)
            print("WARNING: Re-running %begin_axioms does not reset previously defined axioms.")
            print("         It is suggested that you restart and run all cells after editing axioms.")
        print("Defining axioms for theory '" + self.theory.name + "'")
        print("Subsequent end-of-cell assignments will define axioms")
        print("%end_axioms will finalize the definitions")

    def begin_theorems(self):
        # theory based upon current working directory
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'theorems':
                raise ProveItMagicFailure("Run %%begin_theorems in a separate notebook from %%begin_%s."%self.kind)
            print("WARNING: Re-running %begin_theorems does not reset previously defined theorems.")
            print("         It is suggested that you restart and run all cells after editing theorems.")
        print("Defining theorems for theory '" + self.theory.name + "'")
        print("Subsequent end-of-cell assignments will define theorems")
        print("'%end theorems' will finalize the definitions")

    def begin_common(self):
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'common':
                raise ProveItMagicFailure("Run '%%begin common' in a separate notebook from %%begin_%s."%self.kind)
            print("WARNING: Re-running '%begin common' does not reset previously defined common expressions.")
            print("         It is suggested that you restart and run all cells after editing the expressions.")
        print("Defining common sub-expressions for theory '" + self.theory.name + "'")
        print("Subsequent end-of-cell assignments will define common sub-expressions")
        print("%end_common will finalize the definitions")

    def clear(self, kind):
        # theory based upon current working directory
        self.theory = Theory(active_folder=kind)
        if kind == 'axioms':
            self.theory._clearAxioms()
        elif kind == 'theorems':
            self.theory._clearTheorems()
        elif kind == 'common':
            self.theory._clearCommonExressions()
        elif Judgment.theoremBeingProven is not None:
            kind = '_proof_' + Judgment.theoremBeingProven.name
        # clean unreferenced expressions:
        self.theory.clean_active_folder(clear=True)
        self.kind = None
                
    def load_expr(self, kind=None):
        theory_and_folder, hash_id = os.path.split(os.path.abspath('.'))
        _, folder = os.path.split(theory_and_folder)
        theory = Theory(active_folder=folder)
        if kind=='axiom' or kind=='theorem':
            # When checking an axiom or theorem expression, we
            # are doing so within the Axiom or Theorem folder.
            stored_expr = theory.getStoredJudgmentOrProof(hash_id).provenTruth.expr
        else:
            stored_expr = theory.getStoredExpr(hash_id)
        theory.set_active_folder(None)
        self.shell.user_ns['stored_expr'] = stored_expr
        
    def show_proof(self):
        theory_and_folder, hash_id = os.path.split(os.path.abspath('.'))
        _, folder = os.path.split(theory_and_folder)        
        theory = Theory(active_folder=folder)
        show_proof = theory.getShowProof(hash_id)
        theory.set_active_folder(None)
        return show_proof
    
    def proving(self, theorem_name):
        # the theory should be up a directory from the _proofs_ directory
        import proveit
        active_folder = '_proof_' + theorem_name
        self.theory = Theory('..', active_folder=active_folder, owns_active_folder=True) 
        sys.path.append('..')
        try:
            # Disable automation when we are getting this theorem
            # to be proven.
            proveit.defaults.automation = False
            proving_theorem = self.theory.getTheorem(theorem_name)
        finally:
            proveit.defaults.automation = True
        proving_theorem_truth = proving_theorem.provenTruth
        return proving_theorem_truth.beginProof(proving_theorem)
        
    def qed(self):
        import proveit
        proof = Judgment.theoremBeingProven.provenTruth._qed()
        proof._repr_html_() # generate expressions that should be referenced
        # clean unreferenced expressions, but only when "display latex"
        # is enabled (otherwise, references won't be complete).
        if proveit.defaults.display_latex:
            self.theory.clean_active_folder()
        self.theory = None
        return proof

    def end(self, kind):
        '''
        Finish 'axioms', 'theorems', 'common', or other (e.g., 'demonstrations')
        for the Theory associated with the current working directory.
        '''
        import proveit
        if self.kind != kind:
            raise ProveItMagicFailure(r"Must run %begin " + kind + r" before %end " + kind)
        # Add the special statements / expressions to the theory
        theory = self.theory
        if kind=='axioms':
            theory._setAxioms(self.keys, self.definitions)
        elif kind=='theorems':            
            theory._setTheorems(self.keys, self.definitions)
        elif kind=='common':
            # Record the theory names of common expressions referenced
            # by this theory's common expressions notebook...
            theory.recordCommonExprDependencies()
            # and check for illegal mutual references.
            cyclically_referenced_common_expr_theory = self.theory.cyclicallyReferencedCommonExprTheory()
            if cyclically_referenced_common_expr_theory is not None:
                raise ProveItMagicFailure("Not allowed to have cyclically dependent 'common expression' notebooks: %s._common_"%cyclically_referenced_common_expr_theory)
            theory._setCommonExpressions(self.keys, self.definitions)
        
        # clean unreferenced expressions, but only when "display latex"
        # is enabled (otherwise, references won't be complete).
        if proveit.defaults.display_latex:
            self.theory.clean_active_folder()
        
        # Turn off the ownership while remaking expression notebooks.
        theory.set_active_folder(active_folder=kind, owns_active_folder=False)
        if kind in ('axioms', 'theorems', 'common'):
            # Make a _common_.py, _axioms_.py or _theorems_.py for importing
            # expressions from the certified database.
            theory.makeSpecialExprModule(kind)
    	   
            # Update the expression notebooks now that these have been registered
            # as special expressions.
            for name, expr in self.definitions.items():
                print("complete", name)
                # remake the expression notebooks using the special expressions of the theory
                theory.expressionNotebook(expr, nameKindTheory = (name, kind, theory),
                                           completeSpecialExprNotebook=True)  
            
            if len(self.definitions)==0:
                print("Theory %s has no %s"%(theory.name, kind if kind != 'common' else 'common expressions'))
            elif kind=='common':
                print("Common expressions may be imported from autogenerated _%s_.py"%kind)
            else:
                print("%s may be imported from autogenerated _%s_.py"%((kind[0].upper() + kind[1:]), kind))
        self.ranFinish = True       

        if kind=='theorems':
            # stash proof notebooks that are not active theorems.
            self.theory.stashExtraneousThmProofNotebooks()            
        self.kind = None
        self.theory = None
            
    def display_dependencies(self, name, thm_expr):
        '''
        Show the dependencies of an axiom or theorem.
        '''
        proof = thm_expr.proof() # Axiom or Theorem

        from proveit._core_._theory_storage import TheoryFolderStorage
        
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
                display(HTML('<h3>Unproven conjectures required (directly or indirectly) to prove %s</h3>'%name))
                display(HTML('<dl>'))
                for required_unproven_theorem in sorted(required_unproven_theorems, key=stmt_sort):
                    displaySpecialStmt(Theory.findTheorem(required_unproven_theorem))
                display(HTML('</dl>'))
            if len(required_axioms) > 0:
                display(HTML('<h3>Axioms required (directly or indirectly) to prove %s</h3>'%name))
                display(HTML('<dl>'))
                for required_axiom in sorted(required_axioms, key=stmt_sort):       
                    displaySpecialStmt(Theory.findAxiom(required_axiom))
                display(HTML('</dl>'))
        
        dependents = proof.directDependents()
        if len(dependents) == 0:
            display(HTML('<h3>No theorems/conjectures depend upon %s</h3>'%name))
        else:
            display(HTML('<h3>Theorems/conjectures that depend directly on %s</h3>'%name))
            display(HTML('<dl>'))
            for dependent in sorted(proof.directDependents(), key=stmt_sort):
                displaySpecialStmt(Theory.findTheorem(dependent))
            display(HTML('</dl>'))

    def display_dependencies_latex(self, name, thm_expr):
        '''
        Show the dependencies of an axiom or theorem.
        '''
        proof = thm_expr.proof() # Axiom or Theorem
        
        def displaySpecialStmt(stmt):
            '''
            Given an Axiom or Theorem, display HTML with a link
            to the definition.
            '''
            expr = stmt.provenTruth.expr
            print('\item $' + expr.latex() + '$')
        
        def stmt_sort(stmt):
            return str(stmt)
        
        if isinstance(proof, Theorem):
            try:
                required_axioms, required_unproven_theorems = proof.allRequirements()
            except:
                print('This theorem has not been proven yet.')
                required_axioms, required_unproven_theorems = tuple(), tuple()
                
            if len(required_unproven_theorems) > 0:
                print('Unproven conjectures required (directly or indirectly) to prove %s'%name)
                print(r'\begin{itemize}')
                for required_unproven_theorem in sorted(required_unproven_theorems, key=stmt_sort):
                    displaySpecialStmt(Theory.findTheorem(required_unproven_theorem))
                print(r'\end{itemize}')
            if len(required_axioms) > 0:
                print('Axioms required (directly or indirectly) to prove %s'%name)
                print(r'\begin{itemize}')
                for required_axiom in sorted(required_axioms, key=stmt_sort):       
                    displaySpecialStmt(Theory.findAxiom(required_axiom))
                print(r'\end{itemize}')
        
        dependents = proof.directDependents()
        if len(dependents) == 0:
            print('No theorems/conjectures depend upon %s'%name)
        else:
            print('Theorems/conjectures that depend directly on %s'%name)
            for dependent in sorted(proof.directDependents(), key=stmt_sort):
                displaySpecialStmt(Theory.findTheorem(dependent))
    

@magics_class
class ProveItMagic(Magics, ProveItMagicCommands):
    "Magics that hold additional state"

    def __init__(self, shell, assignmentBehaviorModifier):
        # You must call the parent constructor
        Magics.__init__(self, shell)
        ProveItMagicCommands.__init__(self)
        self.assignmentBehaviorModifier = assignmentBehaviorModifier
        assignmentBehaviorModifier.displayAssignments(ip)
    
    @line_magic
    def display_assignments(self, line):
        if line.strip() == 'off':
            self.assignmentBehaviorModifier.resetBehavior()        
        else:
            self.assignmentBehaviorModifier.displayAssignments(self.shell)
    
    @line_magic
    def contents(self, line):
        '''
        Generates a "table of contents" hierarchy of theories for the theories
        listed in the line.
        '''
        ProveItMagicCommands.display_contents(self, line.split())
            
    @line_magic
    def theory(self, line):
        '''
        Create the _common_, _axioms_ and _theorems_ notebooks for the current
        theory (if they do not already exist).  Show the table of contents
        for sub-theories which may be edited.
        '''
        ProveItMagicCommands.display_theory(self)
    
    def _extract_kind(self, line):
        kind = line.strip()
        split_kind = kind.split()
        if len(split_kind) > 1:
            assert split_kind[1][0] == '#' # only comments aloud if there are multiple words on the line
            kind = split_kind[0]
        return kind
    
    @line_magic
    def begin(self, line):
        kind = self._extract_kind(line)
        # theory based upon current working directory
        self.theory = Theory(active_folder=kind, owns_active_folder=True)
        if kind in ('axioms', 'theorems', 'common'):
            from proveit import defaults
            # Unload anything previously loaded from this folder
            # to force it to regenerate expression notebooks,
            # etc.
            self.theory._theoryFolderStorage(kind).unload()
            if defaults.automation:
                raise Exception("The proveit.defaults.automation flag should "
                                "be disabled at the beginning of a "
                                "'common expressions', 'axioms' or 'theorems'"
                                "notebook.")
        if kind == 'axioms':
            self.begin_axioms()
        elif kind == 'theorems':
            self.begin_theorems()
        elif kind == 'common':
            self.begin_common()
        self.kind = kind

    @line_magic
    def end(self, line):
        kind = self._extract_kind(line)
        ProveItMagicCommands.end(self, kind)
        self.theory = None

    @line_magic
    def clear(self, line):
        kind = line.strip()
        ProveItMagicCommands.clear(kind)
    
    @line_magic
    def clean_active_folder(self, line):
        if self.theory is not None:
            self.theory.clean_active_folder()
    
    @line_magic
    def load_expr(self, line):
        ProveItMagicCommands.load_expr(self)

    @line_magic
    def load_common_expr(self, line):
        ProveItMagicCommands.load_expr(self)

    @line_magic
    def load_axiom_expr(self, line):
        ProveItMagicCommands.load_expr(self, 'axiom')

    @line_magic
    def load_theorem_expr(self, line):
        ProveItMagicCommands.load_expr(self, 'theorem')
    
    @line_magic
    def show_expr(self, line):
        return ProveItMagicCommands.show_expr(self)

    @line_magic
    def show_proof(self, line):
        show_proof = ProveItMagicCommands.show_proof(self)
        self.shell.user_ns['show_proof'] = show_proof
        return show_proof
                                                 
    @line_magic
    def proving(self, line):        
        theorem_name = line.strip()
        begin_proof_result = ProveItMagicCommands.proving(self, theorem_name)
        assert isinstance(begin_proof_result, Expression), "Expecting result of 'proving' to be an expression"
        # assign the theorem name to the theorem expression
        # and display this assignment
        self.shell.user_ns[theorem_name] = begin_proof_result
        return Assignments([theorem_name], [begin_proof_result], beginningProof=True)
    
    @line_magic
    def qed(self, line):
        return ProveItMagicCommands.qed(self)

    @line_magic
    def dependencies(self, line):
        '''
        Show the dependencies of an axiom or theorem.
        '''
        name = line.strip()
        thm_expr = self.shell.user_ns[line.strip()]
        ProveItMagicCommands.display_dependencies(self, name, thm_expr)
        
    @line_magic
    def dependencies_latex(self, line):
        '''
        Show the dependencies of an axiom or theorem.
        '''
        name = line.strip()
        thm_expr = self.shell.user_ns[line.strip()]
        ProveItMagicCommands.display_dependencies_latex(self, name, thm_expr)
        
class Assignments:    
    def __init__(self, names, rightSides, beginningProof=False):
        self.beginningProof = beginningProof
        from proveit import singleOrCompositeExpression
        processedRightSides = []
        for rightSide in rightSides:
            if not isinstance(rightSide, Judgment):
                try:
                    # try to combine a composite expression if the right side is a
                    # list or dictionary that should convert to an expression.
                    rightSide = singleOrCompositeExpression(
                            rightSide, wrap_expr_range_in_tuple=False)
                except:
                    pass
            if proveItMagic.kind in ('axioms', 'theorems', 'common'):
                if not isinstance(rightSide, Expression) and (rightSide is not None):
                    # raise ValueError("Right hand side of end-of-cell "
                    #                  "assignment(s) is expected to be "
                    #                  "Expression(s).")
                    raise ValueError("Right hand side of end-of-cell "
                                     "assignment(s) is {}, but is expected to "
                                     "be Expression(s).".format(rightSide))
            processedRightSides.append(rightSide)
        self.names = list(names)
        self.rightSides = processedRightSides
        for name, rightSide in zip(names, self.rightSides):
            if name in proveItMagic.definitions:
                prev_def = proveItMagic.definitions[name]
                if rightSide != prev_def and isinstance(prev_def, Expression):
                    proveItMagic.expr_names[prev_def].remove(name)
                    if len(proveItMagic.expr_names[prev_def]) == 0:
                        proveItMagic.expr_names.pop(prev_def)
            if rightSide is None:
                # unsetting a defintion
                proveItMagic.lowerCaseNames.remove(name.lower())
                prev_def = proveItMagic.definitions[name]
                proveItMagic.definitions.pop(name)
                proveItMagic.keys.remove(name)
                continue
            if proveItMagic.kind == 'axioms' or proveItMagic.kind == 'theorems':
                # Axiom and theorem variables should all be bound
                # though we will only check for variables that are
                # entirely unbound because it would be challenging
                # to consider partially bound instances and it isn't
                # so critical -- it's just a good convention.
                if len(free_vars(rightSide, err_inclusively=False)) > 0:
                    raise ValueError(
                            '%s should not have free variables; variables '
                            'must all be bound (e.g. universally quantified). '
                            ' Free variables: %s'
                            %(proveItMagic.kind, 
                              free_vars(rightSide, err_inclusively=False)))
                if name in proveItMagic.definitions:
                    if proveItMagic.definitions[name] != rightSide:
                        print('WARNING: Redefining', name)
                    proveItMagic.keys.remove(name)
                elif name.lower() in proveItMagic.lowerCaseNames:
                    if not(proveItMagic.ranFinish and name in proveItMagic.definitions): # allowed to come back around after it finished once
                        raise ProveItMagicFailure("%s names must be unique regardless of capitalization"%proveItMagic.kind[:-1])
            proveItMagic.lowerCaseNames.add(name.lower())
            proveItMagic.definitions[name] = rightSide
            if isinstance(rightSide, Expression):
                proveItMagic.expr_names.setdefault(rightSide, []).append(name)
            proveItMagic.keys.append(name)
    
    def html_line(self, name, rightSide):
        lhs_html = name + ':'
        nameKindTheory = None
        kind = proveItMagic.kind
        theory = proveItMagic.theory
        if kind in ('axioms', 'theorems', 'common'):
            if kind=='axioms' or kind=='theorems': kind = kind[:-1]
            nameKindTheory = (name, kind, theory)
        rightSideStr, expr = None, None
        if isinstance(rightSide, Expression):
            expr = rightSide
            rightSideStr = rightSide._repr_html_(unofficialNameKindTheory=nameKindTheory)
        elif hasattr(rightSide, '_repr_html_'):
            rightSideStr = rightSide._repr_html_()
        if rightSideStr is None:
            rightSideStr = str(rightSide)
        num_duplicates = len(proveItMagic.expr_names[rightSide])-1
        if proveItMagic.kind == 'theorems':
            assert expr is not None, "Expecting an expression for the theorem"
            proof_notebook_relurl = theory.thmProofNotebook(name, expr, num_duplicates)
            status = 'conjecture without proof' # default
            try:
                thm = theory.getStoredTheorem(theory.name + '.' + name)
                if thm.isComplete():
                    status = 'established theorem'
                elif thm.hasProof():
                    status = 'conjecture with conjecture-based proof'
            except KeyError:
                pass # e.g., a new theorem.
            lhs_html = ('<a class="ProveItLink" href="%s">%s</a> (%s):<br>'
                        %(proof_notebook_relurl, name, status))
        if self.beginningProof:
            html = 'Under these <a href="presumptions.txt">presumptions</a>, we begin our proof of<br>'
        else:
            html = ''
        html += '<strong id="%s">%s</strong> %s<br>'%(name, lhs_html, rightSideStr)
        if self.beginningProof:
            stored_thm = theory.getStoredTheorem(theory.name + '.' + name)
            dependencies_notebook_path = os.path.join(stored_thm.path, 'dependencies.ipynb')
            html += '(see <a class="ProveItLink" href="%s">dependencies</a>)<br>'%(relurl(dependencies_notebook_path))
        if (kind in ('axiom', 'theorem', 'common')) and num_duplicates > 0:
            prev = proveItMagic.expr_names[rightSide][-2]
            if kind == 'theorem':
                html += '(alternate proof for <a class="ProveItLink" href="#%s">%s</a>)<br>'%(prev, prev)
            elif kind=='axiom':
                print('WARNING: Duplicate of', prev)
        return html

    def _repr_html_(self):
        if len(self.names) == 0: return
        try:
            return '\n'.join(self.html_line(name, rightSide) for name, rightSide in zip(self.names, self.rightSides))
        except Exception as e:
            print(e)
        
    def __repr__(self):
        return '\n'.join('%s: %s'%(name, repr(rightSide)) for name, rightSide in zip(self.names, self.rightSides))

def possibly_wrap_html_display_objects(orig):
    from proveit import ExprTuple
    try:
        if hasattr(orig, '_repr_html_'):
            # No need to wrap.  Already has _repr_html.
            return orig
        all_expr_objs = True
        for obj in orig:
            if not isinstance(obj, Expression):
                all_expr_objs = False
            if not hasattr(obj, '_repr_html_'):
                return orig
        if all_expr_objs:
            # If they are all expression objects, wrap it in
            # an ExprTuple.
            return ExprTuple(*orig)
        return HTML_DisplayObjects(orig)
    except:
        return orig

class HTML_DisplayObjects:
    def __init__(self, objects):
        self.objects = objects
    
    def _repr_html_(self):
        try:
            return '<br>\n'.join(obj._repr_html_() for obj in self.objects)
        except Exception as e:
            print(e)
    
    


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
