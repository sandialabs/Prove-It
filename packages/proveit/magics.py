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
# import new#Comment out for python 3
import types  # Added for python 3
import re
import os
import sys
# from ._theory_storage import relurl#Comment out for Python 3
from proveit._core_._theory_storage import relurl  # Comment in for Python 3


class AssignmentBehaviorModifier:
    def __init__(self):
        self.ipython = ipython = get_ipython()
        # prevent unwanted overwriting when the extension is reloaded
        if not hasattr(ipython, 'orig_run_cell'):
            # remember the original version of 'run_cell'
            ipython.orig_run_cell = ipython.run_cell

    def _setBehavior(self, assignment_fn, last_line_fn):
        ipython = self.ipython

        def new_run_cell(self, raw_cell, *args, **kwargs):
            lines = raw_cell.split('\n')
            # find the last non-indented python statement in the cell
            non_indented_line_indices = [k for k, line in enumerate(
                lines) if len(line) > 0 and re.match(r"\s", line[0]) is None]
            if len(non_indented_line_indices) == 0:
                # no non-indented lines.  just run the cell normally.
                new_raw_cell = '\n'.join(lines)
                return ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
            # get the last non-indented line and all indented lines that follow
            last_python_stmt = '\n'.join(lines[non_indented_line_indices[-1]:])
            # look for one or more variables on the left side of an assignment
            if re.match(
                r"[a-zA-Z_][a-zA-Z0-9_\.]*\s*(,\s*[a-zA-Z_][a-zA-Z0-9_\.]*)*\s*=",
                    last_python_stmt) is not None:
                lhs, rhs = last_python_stmt.split('=', 1)
                if len(rhs) > 0 and rhs[0] != '=':  # "==" doesn't count
                    lhs = lhs.strip()
                    rhs = rhs.strip()
                    if lhs != 'theory' and rhs.find(
                            "proveit.Theory('.')") != 0:
                        lines.append(assignment_fn(
                            [varname.strip() for varname in lhs.split(',')]))
            elif re.match(r"[a-zA-Z_][a-zA-Z0-9_\.]*$", last_python_stmt) is not None:
                # We may alter the last line for dispaly purposes.
                lines.append(last_line_fn(last_python_stmt))
            new_raw_cell = '\n'.join(lines)
            return ipython.orig_run_cell(new_raw_cell, *args, **kwargs)
# ipython.run_cell = new.instancemethod(new_run_cell, ipython)#Comment out
# for python 3
        ipython.run_cell = types.MethodType(
            new_run_cell, ipython)  # Add for python 3

    def reset_behavior(self):
        ipython = self.ipython
        ipython.run_cell = ipython.orig_run_cell

    def display_assignments(self, shell):
        # shell.ex("from proveit._core_.magics import Assignments")#Comment out
        # for Python 3
        shell.ex("import proveit.magics")  # Comment in for Python 3
        self._setBehavior(
            lambda varnames: "proveit.magics.Assignments([" +
            ','.join(
                "'%s'" %
                varname for varname in varnames) +
            "], [" +
            ','.join(varnames) +
            "])",
            lambda orig_last_line: "proveit.magics.possibly_wrap_html_display_objects(%s)" %
            orig_last_line)


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
        self.theory = Theory()  # theory of the current working directory
        self.sub_theory_names = list(self.theory.get_sub_theory_names())
        self.sub_theory_descriptions = dict()

        # read the previous 'mode' (interactive or static) and toggle it.
        prev_mode = 'static'  # default toggles 'static' to 'interactive'
        if os.path.isfile('_mode_.txt'):
            with open('_mode_.txt', 'rt') as f:
                prev_mode = f.read().strip()
        # mode toggles between 'static' and 'interactive'
        if prev_mode == 'static':
            self.mode = 'interactive'
            # in interactive mode, sub-theories are presented in an interactive
            # widget
            self.widget = widgets.VBox()
            self.small_button_layout = widgets.Layout(width='30px')
            self.sub_theory_link_layout = widgets.Layout(width='20%')
            self.sub_theory_description_layout = widgets.Layout(width='80%')
        else:
            self.mode = 'static'

        # write the new mode that has been toggled
        with open('_mode_.txt', 'w') as f:
            f.write(self.mode + '\n')

        # register each sub-theory name, reading their brief descriptions and
        # creating widgets if in interactive mode
        for sub_theory_name in self.sub_theory_names:
            self._add_sub_theoryRow(sub_theory_name)

    def _add_sub_theoryRow(self, sub_theory_name):
        sub_theory_description = self.read_description(sub_theory_name)
        self.sub_theory_descriptions[sub_theory_name] = sub_theory_description
        if self.mode == 'interactive':
            small_button_layout = self.small_button_layout
            sub_theory_link_layout = self.sub_theory_link_layout
            sub_theory_description_layout = self.sub_theory_description_layout
            #rename_button =  widgets.Button(description='', disabled=False, button_style='', tooltip='rename', icon='pencil', layout=small_button_layout)
            up_button = widgets.Button(
                description='',
                disabled=False,
                button_style='',
                tooltip='move up',
                icon='chevron-up',
                layout=small_button_layout)
            dn_button = widgets.Button(
                description='',
                disabled=False,
                button_style='',
                tooltip='move down',
                icon='chevron-down',
                layout=small_button_layout)
            delete_button = widgets.Button(
                description='',
                disabled=False,
                button_style='danger',
                tooltip='delete theory',
                icon='trash',
                layout=small_button_layout)
            href = self.sub_theory_notebook(sub_theory_name)
            sub_theory_link = widgets.HTML(
                '<a class="ProveItLink" href="%s">%s</a>' %
                (href, sub_theory_name), layout=sub_theory_link_layout)
            sub_theory_description = widgets.Text(
                value=sub_theory_description,
                placeholder='Add a brief description here...',
                layout=sub_theory_description_layout)

            def set_description(change):
                self.sub_theory_descriptions[sub_theory_name] = change['new']
                self.write_description_file(sub_theory_name)
            sub_theory_description.observe(set_description, names='value')
            row_widget = widgets.VBox([widgets.HBox(
                [sub_theory_link, sub_theory_description, up_button, dn_button, delete_button])])
            self.widget.children = self.widget.children + (row_widget,)

            def move_up(sender):
                idx = self.sub_theory_names.index(sub_theory_name)
                self.move_up(idx)

            def move_down(sender):
                idx = self.sub_theory_names.index(sub_theory_name)
                self.move_up(idx + 1)

            def delete_sub_theory(sender):
                # before deleting a sub-theory, we need confirmation by
                # entering the sub-theory name
                delete_msg = widgets.Label(
                    "To remove (unlink) sub-theory, enter its name as confirmation",
                    layout={
                        'width': '400px',
                        'max_width': '400px'})
                verification_text = widgets.Text(
                    layout=widgets.Layout(
                        flex_grow=2, max_width='500px'))
                cancel_button = widgets.Button(
                    description='cancel',
                    disabled=False,
                    tooltip='cancel',
                    layout={
                        'width': '80px'})
                cancel_button.on_click(dismiss_delete)
                verification_text.observe(monitor_confirmation)
                row_widget.children = (row_widget.children[0], widgets.HBox(
                    [delete_msg, verification_text, cancel_button], layout={'justify_content': 'flex-end'}))

            def dismiss_delete(sender):
                # dismiss the delete confirmation/message by removing all be
                # the first row in the row_widget
                row_widget.children = (row_widget.children[0],)

            def monitor_confirmation(change):
                # check to see if the user has entered the sub-theory name for
                # confirmation
                if change['new'] == sub_theory_name:
                    # delete theory has been
                    self.delete_sub_theory(sub_theory_name)
            up_button.on_click(move_up)
            dn_button.on_click(move_down)
            delete_button.on_click(delete_sub_theory)

    def sub_theory_notebook(self, sub_theory_name):
        '''
        Returns the path of the _theory_.ipynb notebook for the given sub-theory,
        creating it if necessary.
        '''
        import proveit
        notebook_name = os.path.join(sub_theory_name, '_theory_.ipynb')
        if not os.path.isdir(sub_theory_name):
            os.mkdir(sub_theory_name)
            init_name = os.path.join(sub_theory_name, '__init__.py')
            open(init_name, 'w')
        # Create the generic version from the template
        # (even if we have an existing version so we can update the
        # markdown title if we need to.)
        proveit_path = os.path.split(proveit.__file__)[0]
        with open(os.path.join(proveit_path, '..', '_theory_template_.ipynb'), 'r') as template:
            generic_nb_str = template.read()
            super_theory_links = Theory('.').links(
                from_directory=sub_theory_name)
            generic_nb_str = generic_nb_str.replace(
                '#THEORY#', super_theory_links + '.' + sub_theory_name)
        if os.path.isfile(notebook_name):
            # already exists, but title may need to be updated
            Theory.update_title_if_needed(notebook_name, generic_nb_str)
            return notebook_name
        # write the notebook file
        with open(notebook_name, 'w') as notebook_file:
            notebook_file.write(generic_nb_str)
        return notebook_name

    def add_sub_theory(self, sub_theory_name):
        '''
        Add a new sub-theory with the given name.
        '''
        if sub_theory_name in self.sub_theory_names:
            return
        if sub_theory_name == '':
            return
        self.theory.append_sub_theory_name(sub_theory_name)
        self.sub_theory_names.append(sub_theory_name)
        self._add_sub_theoryRow(sub_theory_name)

    def delete_sub_theory(self, theory_name_to_delete):
        '''
        Delete (unlink) a sub-theory with the given name as long as there are not external
        references to its expressions.  Either way, the directory will remain.
        Only files in the __pv_it directories are cleared (recursively in all sub-sub theories,
        etc) and the current directory's theory will no longer link to it.  That is
        why we use the term 'unlinked'.  It may be resurrected by adding the sub-theory
        with the same name back in.
        '''
        theory = Theory(theory_name_to_delete)
        # remove all internal references and see if any external references
        # remain
        theory.clear_all()
        contains_expressions = theory.contains_any_expression()

        def dismiss(sender):
            if not contains_expressions:
                # Successful removal; we need to remove the deleted sub-theory name from
                # the self.sub_theory_names list, the displayed widgets, and
                # the list in _sub_theories_.txt.
                new_sub_theories = []
                new_widget_children = []
                for k, sub_theory_name in enumerate(self.sub_theory_names):
                    if sub_theory_name != theory_name_to_delete:
                        new_sub_theories.append(sub_theory_name)
                        new_widget_children.append(self.widget.children[k])
                self.sub_theory_names = new_sub_theories
                self.update_sub_theory_names()
                self.widget.children = new_widget_children
            else:
                # dismiss the delete confirmation/message by removing all but
                # the first row in the row_widget
                row_widget.children = (row_widget.children[0],)
        if not contains_expressions:
            msg = 'Removing (unlinking) sub-theory; add it again to resurrect it or delete the directory to make it permanent'
            msg_width = '650px'
        else:
            msg = "Theory removal cancelled; there are external references to its expressions (or corrupted '__pv_it' directories)"
            msg_width = '650px'
        row_widget = self.widget.children[self.sub_theory_names.index(
            theory_name_to_delete)]
        delete_msg = widgets.Label(
            msg,
            layout={
                'width': msg_width,
                'max_width': msg_width})
        gotit_button = widgets.Button(
            description='got it',
            disabled=False,
            tooltip='got it',
            layout={
                'width': '80px'})
        gotit_button.on_click(dismiss)
        row_widget.children = (row_widget.children[0], widgets.HBox(
            [delete_msg, gotit_button], layout=widgets.Layout(justify_content='flex-end')))

    def move_up(self, i):
        if i <= 0 or i == len(self.widget.children):
            return  # can't move the first entry up or go beyond the last entry
        self.widget.children = self.widget.children[:i - 1] + (
            self.widget.children[i], self.widget.children[i - 1]) + self.widget.children[i + 1:]
        self.sub_theory_names = self.sub_theory_names[:i - 1] + [
            self.sub_theory_names[i], self.sub_theory_names[i - 1]] + self.sub_theory_names[i + 1:]
        self.update_sub_theory_names()

    def read_description(self, sub_theory_name):
        brief_description = ''
        brief_description_filename = os.path.join(
            sub_theory_name, '_brief_description_.txt')
        if os.path.isfile(brief_description_filename):
            with open(brief_description_filename) as f2:
                brief_description = f2.read().strip()
        self.sub_theory_descriptions[sub_theory_name] = brief_description
        return brief_description

    def write_description_file(self, sub_theory_name):
        brief_description = self.sub_theory_descriptions[sub_theory_name]
        if brief_description != '':
            brief_description_filename = os.path.join(
                sub_theory_name, '_brief_description_.txt')
            with open(brief_description_filename, 'w') as f:
                f.write(brief_description + '\n')

    def update_sub_theory_names(self):
        '''
        Update the stored sub-theory names (in the _sub_theories_.txt file) with
        self.sub_theory_names
        '''
        # rewrite the sub_theories.txt file with new information.
        self.theory.set_sub_theory_names(self.sub_theory_names)


class ProveItMagicCommands:
    def __init__(self):
        self.reset()

    def reset(self):
        # You must call the parent constructor
        self.kind = None
        self.definitions = dict()  # map name to expression
        self.expr_names = dict()  # map expression to names
        self.keys = []  # the keys of the definitions in the order they appear
        self.lower_case_names = set()
        self.theory = None
        self.ran_finish = False

    def display_contents(self, theory_names):
        '''
        Generates a "table of contents" hierarchy of theories for the theories
        listed in the line.
        '''
        def generate_contents(theories):
            if len(theories) == 0:
                return ''
            html = '<ul>\n'
            for theory in theories:
                href = relurl(
                    os.path.join(
                        theory.get_path(),
                        '_theory_.ipynb'))
                html += '<li><a class="ProveItLink" href="%s">%s</a></li>\n' % (
                    href, theory.name)
                html += generate_contents(list(theory.generate_sub_theories()))
            return html + '</ul>\n'
        display(HTML(generate_contents(
            [Theory(theory_name) for theory_name in theory_names])))

    def display_theory(self):
        '''
        Create the _common_, _axioms_ and _theorems_ notebooks for the current
        theory (if they do not already exist).  Show the table of contents
        for sub-theories which may be edited.
        '''
        import proveit
        proveit.defaults.automation = False  # No need for automation.
        # create an '__init__.py' in the directory if there is not an existing
        # one.
        if not os.path.isfile('__init__.py'):
            open('__init__.py', 'w').close()  # create an empty __init__.py
        theory = Theory()
        proveit_path = os.path.split(proveit.__file__)[0]
        display(HTML('<h3>Local content of this theory</h3>'))
        special_notebook_types = (
            'common', 'axioms', 'theorems', 'demonstrations')
        special_notebook_texts = (
            'common expressions',
            'axioms',
            'theorems',
            'demonstrations')
        for special_notebook_type in special_notebook_types:
            notebook_name = '_%s_.ipynb' % special_notebook_type
            # Create the generic version from the template
            # (even if we have an existing version so we can update the
            # markdown title if we need to.)
            template_name = '_%s_template_.ipynb' % special_notebook_type
            with open(os.path.join(proveit_path, '..', template_name), 'r') as template:
                generic_nb_str = template.read()
                generic_nb_str = generic_nb_str.replace(
                    '#THEORY#', theory.name)
            if os.path.isfile(notebook_name):
                Theory.update_title_if_needed(notebook_name, generic_nb_str)
            else:
                # Write the notebook file which did not previously exist.
                with open(notebook_name, 'w') as notebook_file:
                    notebook_file.write(generic_nb_str)

        theory_interface = TheoryInterface()
        if theory_interface.mode == 'static':
            special_notebooks_html = '<table><tr>\n'
            for special_notebook_type, special_notebook_text in zip(
                    special_notebook_types, special_notebook_texts):
                special_notebooks_html += '<th><a class="ProveItLink" href="_%s_.ipynb">%s</a></th>\n' % (
                    special_notebook_type, special_notebook_text)
            special_notebooks_html += '</tr></table>\n'
            special_notebooks_html += '<h3>Sub-theories</h3>\n'
            if len(theory_interface.sub_theory_names) > 0:
                special_notebooks_html += '<table>\n'
                for name in theory_interface.sub_theory_names:
                    description = theory_interface.sub_theory_descriptions[name]
                    href = theory_interface.sub_theory_notebook(name)
                    special_notebooks_html += '<tr><th><a class="ProveItLink" href="%s">%s</a></th><td>%s</td></tr>\n' % (
                        href, name, description)
                special_notebooks_html += '</table>\n'
            display(HTML(special_notebooks_html))
        else:
            special_notebook_links = []
            full_width_layout = widgets.Layout(width='100%', padding='5px')
            for special_notebook_type, special_notebook_text in zip(
                    special_notebook_types, special_notebook_texts):
                special_notebook_links.append(
                    widgets.HTML(
                        '<a class="ProveItLink" href="_%s_.ipynb">%s</a>' %
                        (special_notebook_type, special_notebook_text), layout=full_width_layout))
            special_notebook_links = widgets.HBox(special_notebook_links)

            sub_theories_label = widgets.HTML('<h3>Sub-theories</h3>')
            #sub_theory_widgets = widgets.VBox(sub_theory_widgets)
            add_theory_widget = widgets.Text(
                value='', placeholder='Add sub-theory...')

            def add_sub_theory(sender):
                theory_interface.add_sub_theory(add_theory_widget.value)
                add_theory_widget.value = ''
            add_theory_widget.on_submit(add_sub_theory)
            #layout = widgets.Layout(display='flex', flex_flow='column-reverse')
            #display(widgets.Button(description='Edit...', disabled=False, button_style='', tooltip='Edit the sub-contents list', layout=layout))
            #layout = widgets.Layout(float='bottom')
            display(widgets.VBox([special_notebook_links,
                                  sub_theories_label,
                                  theory_interface.widget,
                                  add_theory_widget]))

        display(
            HTML('<h3>Axioms contained within this theory and its descendents</h3>'))
        self.display_all_contained_axioms(theory)

        #display(HTML('<h3>Theorems (or conjectures) contained (directly or indirectly) within this theory</h3>'))
        #display(HTML('Also see list of all contained <a href="contain_theorems.ipynb">theorems (or conjectures)</a>.'))

    def display_all_contained_axioms(self, theory):
        count = 0
        for axiom in theory.generate_local_axioms():
            self.display_special_stmt(axiom)
            count += 1
        if count == 0:
            display(HTML('This theory contains no axioms directly.'))
        for sub_theory in theory.generate_sub_theories():
            display(HTML('<h4>%s</h4>' % sub_theory.name))
            count = 0
            for axiom in sub_theory.generate_all_contained_axioms():
                self.display_special_stmt(axiom)
                count += 1
            if count == 0:
                display(HTML('This sub-theory contains no axioms.'))

    def display_all_contained_theorems(self, theory):
        count = 0
        for theorem in theory.generate_local_theorems():
            self.display_special_stmt(theorem)
            count += 1
        if count == 0:
            display(HTML('This theory contains no theorems directly.'))
        for sub_theory in theory.generate_sub_theories():
            display(HTML('<h4>%s</h4>' % sub_theory.name))
            count = 0
            for theorem in sub_theory.generate_all_contained_theorems():
                self.display_special_stmt(theorem)
                count += 1
            if count == 0:
                display(HTML('This sub-theory contains no theorems.'))

    def prepare_notebook(self, kind):
        import proveit
        proveit.defaults.automation = False
        theory = Theory()
        if kind == 'common':
            import_failure_filename = os.path.join(
                theory._theory_folder_storage('common').path,
                'import_failure.txt')
            if os.path.isfile(import_failure_filename):
                # Start with a clean slate
                os.remove(import_failure_filename)
            proveit.defaults._common_import_failure_filename = \
                import_failure_filename
        proveit.defaults._running_proveit_notebook = (theory, kind)

    def begin_axioms(self):
        # theory based upon current working directory
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'axioms':
                raise ProveItMagicFailure(
                    "Run %%begin_axioms in a separate notebook from %%begin_%s." %
                    self.kind)
            print(
                "WARNING: Re-running %begin_axioms does not reset previously defined axioms.")
            print(
                "         It is suggested that you restart and run all cells after editing axioms.")
        print("Defining axioms for theory '" + self.theory.name + "'")
        print("Subsequent end-of-cell assignments will define axioms")
        print("%end_axioms will finalize the definitions")

    def begin_theorems(self):
        # theory based upon current working directory
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'theorems':
                raise ProveItMagicFailure(
                    "Run %%begin_theorems in a separate notebook from %%begin_%s." %
                    self.kind)
            print(
                "WARNING: Re-running %begin_theorems does not reset previously defined theorems.")
            print(
                "         It is suggested that you restart and run all cells after editing theorems.")
        print("Defining theorems for theory '" + self.theory.name + "'")
        print("Subsequent end-of-cell assignments will define theorems")
        print("'%end theorems' will finalize the definitions")

    def begin_common(self):
        if len(self.definitions) > 0 or self.kind is not None:
            if self.kind != 'common':
                raise ProveItMagicFailure(
                    "Run '%%begin common' in a separate notebook from %%begin_%s." %
                    self.kind)
            print(
                "WARNING: Re-running '%begin common' does not reset previously defined common expressions.")
            print(
                "         It is suggested that you restart and run all cells after editing the expressions.")
        print(
            "Defining common sub-expressions for theory '" +
            self.theory.name +
            "'")
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
        elif Judgment.theorem_being_proven is not None:
            kind = '_proof_' + Judgment.theorem_being_proven.name
        # clean unreferenced expressions:
        self.theory.clean_active_folder(clear=True)
        self.kind = None

    def load_expr(self, kind=None):
        theory_and_folder, hash_id = os.path.split(os.path.abspath('.'))
        _, folder = os.path.split(theory_and_folder)
        theory = Theory(active_folder=folder)
        if kind == 'axiom' or kind == 'theorem':
            # When checking an axiom or theorem expression, we
            # are doing so within the Axiom or Theorem folder.
            stored_expr = theory.get_stored_judgment_or_proof(
                hash_id).proven_truth.expr
        else:
            stored_expr = theory.get_stored_expr(hash_id)
        theory.set_active_folder(None)
        self.shell.user_ns['stored_expr'] = stored_expr

    def show_proof(self):
        theory_and_folder, hash_id = os.path.split(os.path.abspath('.'))
        _, folder = os.path.split(theory_and_folder)
        theory = Theory(active_folder=folder)
        show_proof = theory.get_show_proof(hash_id)
        theory.set_active_folder(None)
        return show_proof

    def proving(self, theorem_name):
        # the theory should be up a directory from the _proofs_ directory
        import proveit
        active_folder = '_proof_' + theorem_name
        self.theory = Theory(
            '..',
            active_folder=active_folder,
            owns_active_folder=True)
        sys.path.append('..')
        try:
            # Disable automation when we are getting this theorem
            # to be proven.
            proveit.defaults.automation = False
            proving_theorem = self.theory.get_theorem(theorem_name)
        finally:
            proveit.defaults.automation = True
        proving_theorem_truth = proving_theorem.proven_truth
        return proving_theorem_truth.begin_proof(proving_theorem)

    def qed(self):
        import proveit
        proof = Judgment.theorem_being_proven.proven_truth._qed()
        proof._repr_html_()  # generate expressions that should be referenced
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
            raise ProveItMagicFailure(
                r"Must run %begin " + kind + r" before %end " + kind)
        # Add the special statements / expressions to the theory
        theory = self.theory
        if kind == 'axioms':
            theory._setAxioms(self.keys, self.definitions)
        elif kind == 'theorems':
            theory._setTheorems(self.keys, self.definitions)
        elif kind == 'common':
            theory._set_common_expressions(self.keys, self.definitions)

        # clean unreferenced expressions, but only when "display latex"
        # is enabled (otherwise, references won't be complete).
        if proveit.defaults.display_latex:
            self.theory.clean_active_folder()

        # Turn off the ownership while remaking expression notebooks.
        theory.set_active_folder(active_folder=kind, owns_active_folder=False)
        if kind in ('axioms', 'theorems', 'common'):
            # Make a _common_.py, _axioms_.py or _theorems_.py for importing
            # expressions from the certified database.
            theory.make_special_expr_module(kind)

            # Update the expression notebooks now that these have been registered
            # as special expressions.
            for name, expr in self.definitions.items():
                # remake the expression notebooks using the special expressions
                # of the theory
                theory.expression_notebook(expr, name_kind_theory=(
                    name, kind, theory), complete_special_expr_notebook=True)

            if len(self.definitions) == 0:
                print(
                    "Theory %s has no %s" %
                    (theory.name, kind if kind != 'common' else 'common expressions'))
            elif kind == 'common':
                print(
                    "Common expressions may be imported from autogenerated _%s_.py" %
                    kind)
            else:
                print("%s may be imported from autogenerated _%s_.py" %
                      ((kind[0].upper() + kind[1:]), kind))
        proveit.defaults._running_proveit_notebook = None
        self.ran_finish = True

        if kind == 'theorems':
            # stash proof notebooks that are not active theorems.
            self.theory.stash_extraneous_thm_proof_notebooks()
        self.kind = None
        self.theory = None

    def display_special_stmt(self, stmt, format_type='html'):
        '''
        Given an Axiom or Theorem, display HTML with a link
        to the definition.
        '''
        expr = stmt.proven_truth.expr
        if format_type == 'html':
            display(
                HTML(
                    '<dt><a class="ProveItLink" href="%s">%s</a></dt><dd>%s</dd>' %
                    (stmt.get_link(), str(stmt), expr._repr_html_())))
        elif format_type == 'latex':
            print(r'\item $' + expr.latex() + '$')
        else:
            raise ValueError("Unknown format type: %s" % format_type)

    def display_dependencies(self, name, thm_expr):
        '''
        Show the dependencies of an axiom or theorem.
        '''
        proof = thm_expr.proof()  # Axiom or Theorem

        from proveit._core_._theory_storage import TheoryFolderStorage

        def stmt_sort(stmt):
            return str(stmt)

        if isinstance(proof, Theorem):
            try:
                required_axioms, required_unproven_theorems = proof.all_requirements()
            except BaseException:
                display(HTML('<h3>This theorem has not been proven yet.</h3>'))
                required_axioms, required_unproven_theorems = tuple(), tuple()

            if len(required_unproven_theorems) > 0:
                display(
                    HTML(
                        '<h3>Unproven conjectures required (directly or indirectly) to prove %s</h3>' %
                        name))
                display(HTML('<dl>'))
                for required_unproven_theorem in sorted(
                        required_unproven_theorems, key=stmt_sort):
                    self.display_special_stmt(
                        Theory.find_theorem(required_unproven_theorem))
                display(HTML('</dl>'))
            if len(required_axioms) > 0:
                display(
                    HTML(
                        '<h3>Axioms required (directly or indirectly) to prove %s</h3>' %
                        name))
                display(HTML('<dl>'))
                for required_axiom in sorted(required_axioms, key=stmt_sort):
                    self.display_special_stmt(
                        Theory.find_axiom(required_axiom))
                display(HTML('</dl>'))

        dependents = proof.direct_dependents()
        if len(dependents) == 0:
            display(
                HTML(
                    '<h3>No theorems/conjectures depend upon %s</h3>' %
                    name))
        else:
            display(
                HTML(
                    '<h3>Theorems/conjectures that depend directly on %s</h3>' %
                    name))
            display(HTML('<dl>'))
            for dependent in sorted(proof.direct_dependents(), key=stmt_sort):
                self.display_special_stmt(Theory.find_theorem(dependent))
            display(HTML('</dl>'))

    def display_dependencies_latex(self, name, thm_expr):
        '''
        Show the dependencies of an axiom or theorem.
        '''
        proof = thm_expr.proof()  # Axiom or Theorem

        def stmt_sort(stmt):
            return str(stmt)

        if isinstance(proof, Theorem):
            try:
                required_axioms, required_unproven_theorems = proof.all_requirements()
            except BaseException:
                print('This theorem has not been proven yet.')
                required_axioms, required_unproven_theorems = tuple(), tuple()

            if len(required_unproven_theorems) > 0:
                print(
                    'Unproven conjectures required (directly or indirectly) to prove %s' %
                    name)
                print(r'\begin{itemize}')
                for required_unproven_theorem in sorted(
                        required_unproven_theorems, key=stmt_sort):
                    self.display_special_stmt(
                        Theory.find_theorem(required_unproven_theorem), 'latex')
                print(r'\end{itemize}')
            if len(required_axioms) > 0:
                print(
                    'Axioms required (directly or indirectly) to prove %s' %
                    name)
                print(r'\begin{itemize}')
                for required_axiom in sorted(required_axioms, key=stmt_sort):
                    self.display_special_stmt(
                        Theory.find_axiom(required_axiom), 'latex')
                print(r'\end{itemize}')

        dependents = proof.direct_dependents()
        if len(dependents) == 0:
            print('No theorems/conjectures depend upon %s' % name)
        else:
            print('Theorems/conjectures that depend directly on %s' % name)
            for dependent in sorted(proof.direct_dependents(), key=stmt_sort):
                self.display_special_stmt(
                    Theory.find_theorem(dependent), 'latex')


@magics_class
class ProveItMagic(Magics, ProveItMagicCommands):
    "Magics that hold additional state"

    def __init__(self, shell, assignment_behavior_modifier):
        # You must call the parent constructor
        Magics.__init__(self, shell)
        ProveItMagicCommands.__init__(self)
        self.assignment_behavior_modifier = assignment_behavior_modifier
        assignment_behavior_modifier.display_assignments(ip)

    @line_magic
    def display_assignments(self, line):
        if line.strip() == 'off':
            self.assignment_behavior_modifier.reset_behavior()
        else:
            self.assignment_behavior_modifier.display_assignments(self.shell)

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

    @line_magic
    def common_expressions_notebook(self, line):
        '''
        Prepare for defining common expressions of a theory.
        '''
        ProveItMagicCommands.prepare_notebook(self, 'common')

    @line_magic
    def axioms_notebook(self, line):
        '''
        Prepare for defining axioms of a theory.
        '''
        ProveItMagicCommands.prepare_notebook(self, 'axioms')

    @line_magic
    def theorems_notebook(self, line):
        '''
        Prepare for defining theorems of a theory.
        '''
        ProveItMagicCommands.prepare_notebook(self, 'theorems')

    def _extract_kind(self, line):
        kind = line.strip()
        split_kind = kind.split()
        if len(split_kind) > 1:
            # only comments aloud if there are multiple words on the line
            assert split_kind[1][0] == '#'
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
            self.theory._theory_folder_storage(kind).unload()
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
        assert isinstance(
            begin_proof_result, Expression), "Expecting result of 'proving' to be an expression"
        # assign the theorem name to the theorem expression
        # and display this assignment
        self.shell.user_ns[theorem_name] = begin_proof_result
        return Assignments(
            [theorem_name],
            [begin_proof_result],
            beginning_proof=True)

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
    def __init__(self, names, right_sides, beginning_proof=False):
        self.beginning_proof = beginning_proof
        from proveit import single_or_composite_expression
        processed_right_sides = []
        for right_side in right_sides:
            if not isinstance(right_side, Judgment):
                try:
                    # try to combine a composite expression if the right side is a
                    # list or dictionary that should convert to an expression.
                    right_side = single_or_composite_expression(
                        right_side, wrap_expr_range_in_tuple=False)
                except BaseException:
                    pass
            if prove_it_magic.kind in ('axioms', 'theorems', 'common'):
                if not isinstance(
                        right_side, Expression) and (
                        right_side is not None):
                    # raise ValueError("Right hand side of end-of-cell "
                    #                  "assignment(s) is expected to be "
                    #                  "Expression(s).")
                    raise ValueError("Right hand side of end-of-cell "
                                     "assignment(s) is {}, but is expected to "
                                     "be Expression(s).".format(right_side))
            processed_right_sides.append(right_side)
        self.names = list(names)
        self.right_sides = processed_right_sides
        for name, right_side in zip(names, self.right_sides):
            if name in prove_it_magic.definitions:
                prev_def = prove_it_magic.definitions[name]
                if right_side != prev_def and isinstance(prev_def, Expression):
                    prove_it_magic.expr_names[prev_def].remove(name)
                    if len(prove_it_magic.expr_names[prev_def]) == 0:
                        prove_it_magic.expr_names.pop(prev_def)
            if right_side is None:
                # unsetting a defintion
                prove_it_magic.lower_case_names.remove(name.lower())
                prev_def = prove_it_magic.definitions[name]
                prove_it_magic.definitions.pop(name)
                prove_it_magic.keys.remove(name)
                continue
            if prove_it_magic.kind == 'axioms' or prove_it_magic.kind == 'theorems':
                # Axiom and theorem variables should all be bound
                # though we will only check for variables that are
                # entirely unbound because it would be challenging
                # to consider partially bound instances and it isn't
                # so critical -- it's just a good convention.
                if len(free_vars(right_side, err_inclusively=False)) > 0:
                    raise ValueError(
                        '%s should not have free variables; variables '
                        'must all be bound (e.g. universally quantified). '
                        ' Free variables: %s'
                        % (prove_it_magic.kind,
                           free_vars(right_side, err_inclusively=False)))
                if name in prove_it_magic.definitions:
                    if prove_it_magic.definitions[name] != right_side:
                        print('WARNING: Redefining', name)
                    prove_it_magic.keys.remove(name)
                elif name.lower() in prove_it_magic.lower_case_names:
                    # allowed to come back around after it finished once
                    if not(
                            prove_it_magic.ran_finish and name in prove_it_magic.definitions):
                        raise ProveItMagicFailure(
                            "%s names must be unique regardless of capitalization" % prove_it_magic.kind[:-1])
            prove_it_magic.lower_case_names.add(name.lower())
            prove_it_magic.definitions[name] = right_side
            if isinstance(right_side, Expression):
                prove_it_magic.expr_names.setdefault(
                    right_side, []).append(name)
            prove_it_magic.keys.append(name)

    def html_line(self, name, right_side):
        lhs_html = name + ':'
        name_kind_theory = None
        kind = prove_it_magic.kind
        theory = prove_it_magic.theory
        if kind in ('axioms', 'theorems', 'common'):
            if kind == 'axioms' or kind == 'theorems':
                kind = kind[:-1]
            name_kind_theory = (name, kind, theory)
        right_side_str, expr = None, None
        if isinstance(right_side, Expression):
            expr = right_side
            right_side_str = right_side._repr_html_(
                unofficial_name_kind_theory=name_kind_theory)
        elif hasattr(right_side, '_repr_html_'):
            right_side_str = right_side._repr_html_()
        if right_side_str is None:
            right_side_str = str(right_side)
        if kind in ('axiom', 'theorem', 'common'):
            num_duplicates = len(prove_it_magic.expr_names[right_side]) - 1
        if prove_it_magic.kind == 'theorems':
            assert expr is not None, "Expecting an expression for the theorem"
            proof_notebook_relurl = theory.thm_proof_notebook(
                name, expr, num_duplicates)
            status = 'conjecture without proof'  # default
            try:
                thm = theory.get_stored_theorem(theory.name + '.' + name)
                if thm.is_complete():
                    status = 'established theorem'
                elif thm.has_proof():
                    status = 'conjecture with conjecture-based proof'
            except KeyError:
                pass  # e.g., a new theorem.
            lhs_html = ('<a class="ProveItLink" href="%s">%s</a> (%s):<br>'
                        % (proof_notebook_relurl, name, status))
        if self.beginning_proof:
            html = 'Under these <a href="presumptions.txt">presumptions</a>, we begin our proof of<br>'
        else:
            html = ''
        html += '<strong id="%s">%s</strong> %s<br>' % (
            name, lhs_html, right_side_str)
        if self.beginning_proof:
            stored_thm = theory.get_stored_theorem(theory.name + '.' + name)
            dependencies_notebook_path = os.path.join(
                stored_thm.path, 'dependencies.ipynb')
            html += '(see <a class="ProveItLink" href="%s">dependencies</a>)<br>' % (
                relurl(dependencies_notebook_path))
        if (kind in ('axiom', 'theorem', 'common')) and num_duplicates > 0:
            prev = prove_it_magic.expr_names[right_side][-2]
            if kind == 'theorem':
                html += '(alternate proof for <a class="ProveItLink" href="#%s">%s</a>)<br>' % (prev, prev)
            elif kind == 'axiom':
                print('WARNING: Duplicate of', prev)
        return html

    def _repr_html_(self):
        if len(self.names) == 0:
            return
        try:
            return '\n'.join(
                self.html_line(
                    name, right_side) for name, right_side in zip(
                    self.names, self.right_sides))
        except Exception as e:
            print(e)

    def __repr__(self):
        return '\n'.join('%s: %s' % (name, repr(right_side))
                         for name, right_side in zip(self.names, self.right_sides))


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
    except BaseException:
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
    assignment_behavior_modifier = AssignmentBehaviorModifier()
    prove_it_magic = ProveItMagic(ip, assignment_behavior_modifier)
    ip.register_magics(prove_it_magic)


class ProveItMagicFailure(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return self.message
