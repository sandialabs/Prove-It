'''
Build the Prove-It notebooks (common expressions, axioms, theorems,
and proofs) for the given theories, including sub-theories.
'''

from __future__ import print_function
import sys
import os
import subprocess
import itertools
import re
import time
#import lxml  # Comment in for Python 3
#from lxml import etree  # Comment in for Python 3
import shutil
import argparse
import nbformat
from nbconvert.preprocessors import Preprocessor, ExecutePreprocessor
#from nbconvert.preprocessors.execute import executenb
from nbconvert import HTMLExporter
import IPython
from IPython.lib.latextools import LaTeXTool
import base64
import datetime
import tarfile
import urllib#Comment out for Python 3
#import urllib.request  # Comment in for Python 3
import zmq  # to catch ZMQError which randomly occurs when starting a Jupyter kernel
import proveit
from proveit import Theory

# IPython.InteractiveShell.cache_size=0

# for compiling LaTeX
LaTeXTool.clear_instance()
lt = LaTeXTool.instance()
lt.use_breqn = False

default_paths = ['packages/proveit', 'tutorial']  # , 'tutorial/socks_demo']


def find_theory_paths(path):
    if os.path.isdir(os.path.join(path, '_theory_nbs_')):
        yield path
        sub_theories_txt = os.path.join(path, '_sub_theories_.txt')
        if os.path.isfile(sub_theories_txt):
            for sub_theory in open(sub_theories_txt).readlines():
                sub_theory = sub_theory.rstrip()  # strip off the carriage return
                sub_theory_path = os.path.join(path, sub_theory)
                for theory_path in find_theory_paths(sub_theory_path):
                    yield theory_path


# regular expression for finding 'a' html tags; trivially adapted from
# http://haacked.com/archive/2004/10/25/usingregularexpressionstomatchhtml.aspx/
atag_re = r"""<a((\s+\w+(\s*=\s*(?:".*?"|'.*?'|[\^'">\s]+))?)+\s*|\s*)/?>"""
imgtag_re = r"""<img((\s+\w+(\s*=\s*(?:".*?"|'.*?'|[\^'">\s]+))?)+\s*|\s*)/?>"""


"""
def revised_proof_nb(nb, notebook_path):
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'markdown':
            cell.source = cell.source.replace('\\\\', '\\')
            cell.source = cell.source.replace('\\"', '"')
        new_cells.append(cell)
    nb.cells = new_cells
    return nb
"""
"""
def revised_special_nb(nb, notebook_path):
    # this is temporarily needed for some backwards compatibility
    new_cells = []
    for cell in nb.cells:
        cell = cell.copy() # copy the cell and possibly edit the copy
        if cell.cell_type == 'code':
            cell.source = cell.source.replace('%begin_', '%begin ')
            cell.source = cell.source.replace('%end_', '%end ')
        new_cells.append(cell)
    nb.cells = new_cells
    return nb
"""


class ProveItHTMLPreprocessor(Preprocessor):
    '''
    The Prove-It HTML processor will change links from ipynb
    to html and remove "target=blank".  Further, it is used to
    consolidate style information.
    '''

    def __init__(self, strip_links=False, make_images_inline=False):
        self.strip_links = strip_links
        self.make_images_inline = make_images_inline
        self.path = '.'

    def _process_atags(self, text):
        '''
        Search the text for html a-tags of the ProveItLink class.
        For each of these, replace .ipynb with .html and remove
        any target='_blank' (so it does not create a new tab
        in the browser).  Return the new version of the text.
        '''
        new_text = ''
        last_pos = 0
        text = str(text)
        for atag_match in re.finditer(atag_re, text):
            atag = text[atag_match.start():atag_match.end()]
            new_text += text[last_pos:atag_match.start()]
            # parse the a tag with a xml parser
            atag_root = lxml.etree.fromstring(atag + '</a>')
            if 'class' in atag_root.attrib and atag_root.attrib['class'] == 'ProveItLink':
                if '.ipynb' in atag_root.attrib['href']:
                    # replace the .ipynb extension in the href with .html
                    atag_root.attrib['href'] = atag_root.attrib['href'].replace(
                        '.ipynb', '.html')
                    # also, if the .ipynb link uses target='blank', nix that.
                    if 'target' in atag_root.attrib and atag_root.attrib['target'] == '_blank':
                        atag_root.attrib.pop('target')
                    atag = lxml.etree.tostring(atag_root)
                    if atag[-2:] != b'/>':
                        raise Exception(
                            "Expecting '/>' at end of remade xml a-tag")
                    # remove the / before >
                    atag = atag[:-2].decode('ascii') + '>'
            if not self.strip_links:
                new_text += atag
            last_pos = atag_match.end()
        new_text += text[last_pos:]
        if self.strip_links:
            # strip the </a>'s as well as the <a ...>'s
            return re.sub('</a>', '', new_text)
        else:
            return new_text

    def _remove_tags(self, text):
        '''
        Remove html tags from the text.
        '''
        p = re.compile(r'<.*?>')
        return p.sub('', text)

    """
    def _process_latex(self, text):
        '''
        Search the markdown for '$...$' indicating LaTeX.  Generate a png in place of the LaTeX.
        '''
        revised_text = ''
        cur_pos = 0
        latex_start = text.find('$')
        while latex_start >= 0:
            latex_end = text.find('$', latex_start+1)
            latex = text[latex_start+1:latex_end]
            png = latex_to_png(latex, backend='dvipng', wrap=True) # the 'matplotlib' backend can do some BAD rendering in my experience (like \lnot rendering as lnot in some theories)
            revised_text += text[cur_pos:latex_start]
            revised_text += '<img style="vertical-align:text-bottom; display:inline;" src="data:image/png;base64,%s"/>'%base64.b64encode(png)
            cur_pos = latex_end+1
            latex_start = text.find('$', cur_pos)
        revised_text += text[cur_pos:]
        return revised_text
    """

    def _inline_images(self, text):
        '''
        Convert imported images to inline pngs.
        '''
        new_text = ''
        last_pos = 0
        text = str(text)
        for imgtag_match in re.finditer(imgtag_re, text):
            imgtag = text[imgtag_match.start():imgtag_match.end()]
            # print imgtag
            new_text += text[last_pos:imgtag_match.start()]
            # parse the img tag with a xml parser
            imgtag_root = lxml.etree.fromstring(imgtag)
            if 'src' in imgtag_root.attrib:
                png = open(
                    os.path.join(
                        self.path,
                        imgtag_root.attrib['src']),
                    'rb').read()
                imgtag_root.attrib['src'] = "data:image/png;base64,%s" % base64.b64encode(
                    png)
                imgtag = lxml.etree.tostring(imgtag_root)
            # print imgtag
            new_text += imgtag
            last_pos = imgtag_match.end()
        new_text += text[last_pos:]
        return new_text

    def preprocess(self, nb, resources):
        proveit_path = os.path.split(proveit.__file__)[0]
        new_cells = []
        empty_cells = []  # skip empty cells at the end for a cleaner look
        title = None  # take the first line of the first cell to be the title
        for cell in nb.cells:
            cell = cell.copy()  # copy the cell and possibly edit the copy
            if cell.cell_type == 'markdown':
                if title is None:
                    title = self._remove_tags(cell.source.split('\n')[0])
                # process a-tags in markdown cell source, as well as LaTeX.
                # self._process_latex(self._process_atags(cell.source))
                cell.source = self._process_atags(cell.source)
            if cell.cell_type == 'code':
                if len(cell.source) == 0:
                    # an empty cell.  if it is at the end, these will be
                    # skipped altogether for a cleaner look
                    empty_cells.append(cell)
                    continue
                if 'outputs' in cell:
                    for output in cell['outputs']:
                        if 'data' in output and 'text/html' in output.data:
                            # process a-tags in html output
                            output.data['text/html'] = self._process_atags(
                                output.data['text/html'])
                            if self.make_images_inline:
                                # make all images inline
                                output.data['text/html'] = self._inline_images(
                                    output.data['text/html'])
            if len(empty_cells) > 0:
                # fill in empty cells which are not at the end
                new_cells.extend(empty_cells)
                empty_cells = []
            new_cells.append(cell)
        nb.cells = new_cells
        resources['today'] = str(datetime.datetime.today()).split()[0]
        resources['title'] = title
        index_path = os.path.join(proveit_path, '..', '..', 'index.html')
        logo_path = os.path.join(proveit_path, '..', '..', 'pv_it.png')
        if self.path == '':
            self.path = '.'
        relpath_to_index = os.path.relpath(index_path, self.path)
        relpath_to_logo = os.path.relpath(logo_path, self.path)
        resources['relpath_to_index'] = relpath_to_index
        resources['relpath_to_logo'] = relpath_to_logo
        return nb, resources


html_exporter = HTMLExporter(preprocessors=[ProveItHTMLPreprocessor()])
html_exporter.template_file = 'proveit_html'

def is_git_diff_empty(notebook_path):
    '''
    Return true if "git diff" for the given file is empty
    (after filtering if there is filtering as there should be
    for Jupyter notebooks).
    '''
    process = subprocess.Popen(["git", "diff", notebook_path],
                               stdout=subprocess.PIPE)
    output = process.communicate()[0]
    output = re.sub('^diff --git .*$', '', output.decode('utf-8'))
    return output == ""

def git_clear_notebook(notebook_path):
    '''
    If "git diff" is empty after filtering (e.g., the Jupyter notebook 
    only differs in its output), do "git add" to clear it from the list
    of modified files.
    '''
    try:
        # If the file is in a git repository which is filtering
        # the notebook output, see if the only change is in
        # the output.  In that case, 'git add' the file so it
        # doesn't show up as modified.
        if is_git_diff_empty(notebook_path):
            # No change except perhaps filtered output.
            # Do "git add" so it won't show up as different.
            process = subprocess.Popen(['git', 'add', notebook_path])
            print("Clearing filtered notebook-output modifications in git:"
                  "\n\tgit add %s" % notebook_path)
            process.wait()
    except BaseException:
        # Our git check may fail because maybe it isn't in a git
        # repository.  In that case, don't worry about it.
        pass


class KernelStart_failure(Exception):
    def __init__(self):
        pass


class RecyclingExecutePreprocessor(ExecutePreprocessor):
    def __init__(self, **kwargs):
        ExecutePreprocessor.__init__(self, **kwargs)

    def __enter__(self):
        try:
            self.km, self.kc = self.start_new_kernel()
        except RuntimeError:
            raise KernelStart_failure()
        return self

    def __exit__(self, exception_type, exception_value, traceback):
        self.kc.stop_channels()
        self.km.shutdown_kernel()
        self.km, self.kc = None, None

    def preprocess(self, nb, resources, path, display_latex):
        # Record initial loaded modules, including the proveit defaults and
        # proveit.magics.  All other modules will be deleted when
        # we are done so we can "recycle" our Kernel to be used cleanly
        # for the next notebook.

        init_modules_source = """
import sys
from proveit import *
from proveit import defaults
defaults.display_latex=%s
import proveit.magics
__init_modules = list(sys.modules.keys())
__init_modules # avoid Prove-It magic assignment
""" % display_latex

        init_modules_cell = nbformat.NotebookNode(
            cell_type='code', source=init_modules_source, metadata=dict())
        self.preprocess_cell(init_modules_cell, resources, 0)

        # change the working directory
        cd_source = 'import os\nos.chdir(r\"' + path + '")'
        cd_cell = nbformat.NotebookNode(
            cell_type='code', source=cd_source, metadata=dict())
        self.preprocess_cell(cd_cell, resources, 0)

        try:
            # Execute each cell.  We must correct the execution count so we treat this
            # like it was the only notebook executed in this session (even though we
            # are actually recycling the Kernel).
            exec_count = 0
            for index, cell in enumerate(nb.cells):
                if hasattr(cell, 'source') and cell['source'].strip() != '':
                    cell, resources = self.preprocess_cell(
                        cell, resources, index)
                    if 'execution_count' in cell:
                        # make proper execution counts
                        exec_count += 1
                        cell['execution_count'] = exec_count
                        if 'outputs' in cell:
                            for output in cell['outputs']:
                                if 'execution_count' in output:
                                    output['execution_count'] = exec_count
                nb.cells[index]

            if display_latex:
                # for notebooks with no %end or %qed
                clean_cell = nbformat.NotebookNode(
                    cell_type='code', source="%clean_active_folder\n",
                    metadata=dict())
                cell, _ = self.preprocess_cell(clean_cell, resources, 0)
        finally:
            # "reset" the stored Prove-It data.  Also,
            # Delete all modules except those that were initially loaded.
            # Also, %reset local variables and history.
            # We are preparing the Kernel to be recycled.
            reset_source = """
import sys
import proveit
proveit.reset()
# delete all modules but initial modules and proveit._core_ modules
for m in list(sys.modules.keys()):
    if m not in __init_modules:
        if '.' in m:
            parent, child = m.rsplit('.', 1)
            if parent in __init_modules:
                # remove the module being deleted from its parent package
                sys.modules[parent].__dict__.pop(child, None)
        del(sys.modules[m])
%reset
%reset in
%reset out
    """
            reset_cell = nbformat.NotebookNode(
                cell_type='code', source=reset_source, metadata=dict())
            cell, _ = self.preprocess_cell(reset_cell, resources, 0)

            # Garbage collect.
            garbage_collect_source = """import sys
import gc
gc.collect()
len(gc.get_objects()) # used to check for memory leaks
    """
            garbage_collect_cell = nbformat.NotebookNode(
                cell_type='code', source=garbage_collect_source, metadata=dict())
            cell, _ = self.preprocess_cell(garbage_collect_cell, resources, 0)
            # Useful debugging to check for memory leaks:
            #print('num gc objects', cell['outputs'][0]['data']['text/plain'])
        return nb, resources

    def execute_notebook(self, notebook_path, no_latex=False, git_clear=True):
        '''
        Read, execute, and write out the notebook at the given path.
        Return the notebook object.
        '''
        print("Executing", notebook_path)
        start_time = time.time()

        # Read in the notebook.
        with open(notebook_path, encoding='utf8') as f:
            nb_str = f.read().rstrip()
        nb = nbformat.reads(nb_str, as_version=4)

        # execute using a KernelManager with the appropriate cwd (current
        # working directory)
        notebook_dir = os.path.abspath(os.path.split(notebook_path)[0])
        resources = dict()
        while True:
            try:
                #executenb(nb, cwd=notebook_dir)
                self.preprocess(nb, resources, notebook_dir, not no_latex)
                break
            except zmq.ZMQError:
                print("ZMQError encountered")
                pass
                # execute_processor.km.restart_kernel(newport=True)
            except RuntimeError:
                print("Try restarting kernel")
                pass
                # execute_processor.km.restart_kernel(newport=True)
        new_nb_str = nbformat.writes(nb)
        if new_nb_str != nb_str:
            # Write it out if it has changed.
            with open(notebook_path, 'wt', encoding='utf8') as f:
                f.write(new_nb_str)
        print("\tFinished %s in %0.2f seconds" %
              (notebook_path, time.time() - start_time))

        if git_clear:
            git_clear_notebook(notebook_path)

        return nb


def generate_css_if_missing(path):
    # check if there is a notebook.css file in the directory
    css_filename = os.path.join(path, 'notebook.css')
    if not os.path.isfile(css_filename):
        # create a notebook.css that links to a css file of the
        # same name in the directory above it.
        with open(css_filename, 'wt') as f:
            f.write('@import url("../notebook.css")\n')
        generate_css_if_missing(os.path.split(path)[0])


def export_notebook_to_html(
        notebook_path,
        nb=None,
        strip_links=False,
        make_images_inline=False):
    '''
    Export the notebook to html provided the notebook path.
    The notebook object (nb) may be provided, or it will be
    read in from the file.
    '''
    start_time = time.time()
    orig_strip_links = html_exporter.preprocessors[0].strip_links
    orig_make_images_inline = html_exporter.preprocessors[0].make_images_inline
    try:
        html_exporter.preprocessors[0].strip_links = strip_links
        html_exporter.preprocessors[0].make_images_inline = make_images_inline
        html_exporter.preprocessors[0].path = os.path.split(notebook_path)[0]
        if nb is None:
            # read in if it wasn't provided
            with open(notebook_path, encoding='utf8') as f:
                nb = nbformat.read(f, as_version=4)
        # export to HTML
        (body, resources) = html_exporter.from_notebook_node(nb)
        with open(os.path.splitext(notebook_path)[0] + '.html', 'wt',
                  encoding='utf8') as f:
            f.write(body)
        generate_css_if_missing(os.path.split(notebook_path)[
                                0])  # add notebook.css if needed
    finally:
        html_exporter.preprocessors[0].strip_links = orig_strip_links
        # revert back to what it was
        html_exporter.preprocessors[0].make_images_inline = orig_make_images_inline
    print(
        'Exported',
        notebook_path,
        'to HTML in %0.2f seconds' %
        (time.time() -
         start_time))


def execute_and_export_notebook(
        execute_processor,
        notebook_path,
        no_execute=False,
        no_latex=False,
        git_clear=True):
    '''
    Read, execute, and rewrite a notebook and also export it
    to HTML.
    '''
    if no_execute:
        export_notebook_to_html(notebook_path)
    else:
        nb = execute_processor.execute_notebook(notebook_path,
                                                no_latex=no_latex,
                                                git_clear=git_clear)
        export_notebook_to_html(notebook_path, nb)


def execute_and_maybe_export_notebook(
        execute_processor, notebook_path, no_execute=False, no_latex=False,
        git_clear=True, export_to_html=True):
    '''
    Read, execute, and rewrite a notebook and also export it
    to HTML.
    '''
    theory_notebook_name = 'theory.ipynb'
    if notebook_path[-len(theory_notebook_name):] == theory_notebook_name:
        # This is a theory notebook.
        # Set the mode to 'interactive' so it will toggle to 'static' mode
        # when we execute this theory notebook.
        with open(os.path.join(os.path.split(notebook_path)[0], '_mode_.txt'),
                  'wt') as f:
            f.write('interactive\n')
    if export_to_html:
        execute_and_export_notebook(execute_processor, notebook_path,
                                    no_latex=no_latex, no_execute=no_execute,
                                    git_clear=git_clear)
    elif not no_execute:
        execute_processor.execute_notebook(
            notebook_path, no_latex=no_latex, git_clear=git_clear)


"""
def revise_proof_notebook(notebook_path):
    print notebook_path
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    nb = revised_proof_nb(nb, notebook_path)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)
"""

"""
def revise_special_notebook(notebook_path):
    print notebook_path
    with open(notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    nb = revised_special_nb(nb, notebook_path)
    with open(notebook_path, 'wt') as f:
        nbformat.write(nb, f)
"""


def fix_theory(theory_path):
    mode = None
    with open(os.path.join(theory_path, '_sub_theories_.txt')) as f:
        sub_theory_names = []
        for k, line in enumerate(f.readlines()):
            if k == 0 and line[:6] == 'mode: ':
                mode = line[6:].strip()
            else:
                sub_theory_names.append(line.strip())
        Theory(theory_path).set_sub_theory_names(sub_theory_names)
    if mode is not None:
        with open(os.path.join(theory_path, '_mode_.txt'), 'w') as fw:
            fw.write(mode + '\n')


def record_presuming_info(theorem, proof_notebook_path):
    '''
    Given a Theorem object and corresponding proof notebook path,
    record the presuming information from information on the
    "%proving" command line.  We need to execute preceeding commands
    because some of the presumed things may be local variables generated
    in the notebook.
    '''
    with open(proof_notebook_path) as f:
        nb = nbformat.read(f, as_version=4)
    print("Record presuming info:", proof_notebook_path)

    # use '__' to prepend important local variables because we will start
    # running exec on user code and we don't want to pollute our locals.
    __owd = os.getcwd()
    os.chdir(os.path.split(proof_notebook_path)[0])
    __theorem = theorem
    try:
        for __cell in nb['cells']:
            if __cell['cell_type'] == 'code':
                __cellsource = __cell['source']
                __locls = locals()
                __begin_proof_str = '%proving '
                if __cellsource[:len(
                        __begin_proof_str)] == __begin_proof_str or '\n%proving' in __cellsource:
                    __start = __cellsource.find("%proving")
                    exec(__cellsource[:__start])
                    # intercept the proving command
                    __line = __cellsource[__start + len(__begin_proof_str):]
                    __theorem_name, __presuming_str = str(
                        __line.strip()).split(' ', 1)
                    if __theorem_name != __theorem.name:
                        raise ValueError(
                            "Theorem name, %s, does not match expectation, %s, according to filename" %
                            (__theorem_name, theorem.name))
                    if not __presuming_str.find('presuming ') == 0:
                        raise ValueError(
                            "Bad presuming format: %s" %
                            __presuming_str)
                    __args = __presuming_str.split(
                        ' ', 1)[-1].strip('[]').split(',')
                    __args = [__arg.strip(" \\\n") for __arg in __args]
                    __presumptions = [__arg for __arg in __args if __arg != '']
                    # Some of the presumptions are simply strings, but some are local variables
                    # we need to extract.  That is why we had to execute the
                    # previous lines.
                    __presumptions = [str(__locls[__presumption].proof(
                    )) if __presumption in __locls else __presumption for __presumption in __presumptions]
                    __theorem.proven_truth.begin_proof(
                        __theorem, __presumptions, just_record_presuming_info=True)
                    return
                # skip other magic commands (only the imports should really
                # matter)
                elif __cellsource[0] != '%':
                    exec(__cellsource)
    finally:
        os.chdir(__owd)

def extract_tar_with_limitations(filename, paths):
    '''
    Extract the given tar file into the directory of this 'build.py'
    script.  There are some limitations.  Other than files in the
    database (the '__pv_it' folders), only .ipynb, .html, and .css
    files will be extracted, and only if there is an empty 'git diff'
    for Jupyter notebooks (and associated .html files).  Assuming
    notebook output is filtered for 'git diff', this means that
    we only extract notebooks whose output may differ.  Within the
    '__pv_it' folders, we do check for hash collisions (which
    should be astronomically rare) and raise an exception if it should
    occur (why not play it safe).  Also, we skip over anything that 
    isn't within the specified paths.
    '''
    try:
        from mpi4py import MPI
        comm = MPI.COMM_WORLD
        rank = comm.Get_rank()
        nranks = comm.Get_size()
    except BaseException:
        rank, nranks = 0, 1
    tar = tarfile.open(filename)
    # extract into the directory of this 'build.py'
    extract_to_path = os.path.dirname(os.path.realpath(__file__))
    print("Extracting tarball into %s" % extract_to_path)
    prefix = "Prove-It-master-full"
    paths = [os.path.normpath(_path) for _path in paths]
    def tar_member_generator():
        for k, tar_member in enumerate(tar.getmembers()):
            # Divy up the work when multiple cores are used.
            if k%nranks != rank:
                continue
            # drop the first part of the path
            assert tar_member.name.startswith(prefix), (
                    "Expecting tar member names to start with %s"
                    %prefix)
            tar_member.name = tar_member.name[len(prefix)+1:]
            member_path = os.path.normpath(tar_member.name)
            is_contained_in_a_theory_path = False
            for _path in paths:
                if member_path.startswith(_path):
                    is_contained_in_a_theory_path = True
                    break
            if not is_contained_in_a_theory_path:
                continue
            member_fullpath = os.path.join(extract_to_path, member_path)
            member_folder, member_filename = os.path.split(member_path)
            filebase, ext = os.path.splitext(member_filename)
            # The '__pv_it' folder store Prove-It "database"
            # information.
            in_database_folder = ('__pv_it' in member_path.split(os.sep))
            # Extract files in '__pv_it' folders or
            # '.ipynb' and '.html' files.
            if (in_database_folder or
                    ext in ('.ipynb', '.html', '.css')):
                if (not in_database_folder and ext == '.ipynb' 
                        or ext == '.html'):
                    # If this is a notebook or notebook html
                    # not in the database, only extract it if
                    # it is consistent with the git index
                    # version.
                    if ext == '.html':
                        notebook_path = os.path.join(member_folder, 
                                                     filebase + '.ipynb')
                    elif ext == '.ipynb':
                        notebook_path = member_fullpath
                    if os.path.isfile(notebook_path):
                        if not is_git_diff_empty(notebook_path):
                            # Skip this extraction since it
                            # isn't committed.
                            print("Skipping", tar_member.name)
                            continue
                unique_rep = None
                if (in_database_folder and
                        member_filename == 'unique_rep.pv_it'):
                    if os.path.isfile(member_fullpath):
                        with open(member_fullpath, 'r') as f:
                            unique_rep = f.read()
                print('Extracting', tar_member.name)
                yield tar_member
                if unique_rep is not None:
                    # If the unique_rep has change, it seems
                    # there was a hash collision; that should
                    # be astronomically rare!
                    with open(member_fullpath, 'r') as f:
                        new_unique_rep = f.read()
                    if new_unique_rep != unique_rep:
                        raise Exception("There was a hash collision:\n%s\n%s\n"
                              "apparently had the same hash.\n"
                              "Wow!  That should be astronomically "
                              "rare.  A 'build.py --clean' is "
                              "recommended before continuing to "
                              "ensure there are no bad links in the "
                              "Prove-It database.\n"
                              "You may then want to checkout master, do"
                              "'build.py --download', and go from there."%
                              (unique_rep, new_unique_rep))    
                if (not in_database_folder and ext == '.ipynb'):
                    git_clear_notebook(member_fullpath)
    tar.extractall(path=extract_to_path, members=tar_member_generator())

"""
def extract_tar_test(filename, paths):
    '''
    TEST
    '''
    tar = tarfile.open(filename)
    # extract into the directory of this 'build.py'
    extract_to_path = os.path.dirname(os.path.realpath(__file__))
    extract_to_path = os.path.join(extract_to_path, 'tmp')
    print("Extracting tarball into %s" % extract_to_path)
    def tar_member_generator():
        for tar_member in tar.getmembers():
            print(tar_member)
            yield tar_member
    tar.extractall(path=extract_to_path, members=tar_member_generator())
"""

def sure_you_want_to_extract(paths):
    print("WARNING: You will be extracting a tarball that will "
          "overwrite Prove-It database files, Jupyter notebooks, \n"
          "and html/css files into these folders: %s.\n"
          "To be safe, only notebooks that are "
          "the same as the git index up to filtering (e.g., the output "
          "cells)\n"
          "will be replaced, but you should still be careful.\n"
          %paths)
    
    response = input("Are you sure you want to continue? ")
    if response == "": return False
    return response[0].upper()=='Y'  

def mpi_build(
        notebook_paths,
        no_latex=False,
        git_clear=True,
        no_execute=False,
        export_to_html=True):
    try:
        from mpi4py import MPI
        comm = MPI.COMM_WORLD
        rank = comm.Get_rank()
        nranks = comm.Get_size()
    except BaseException:
        rank, nranks = 0, 1

    assert export_to_html or not no_execute, "Nothing to do, in that case??"

    # Set of notebooks that should be attempted after prerequisites
    # have been satisfied (e.g., other common expression notebooks):
    retry_notebooks = set()
    # Map notebooks, to be retried, to theory names:
    retry_notebook_to_theory_name = dict()
    # Map notebooks that need to be retried to their original error
    # message:
    retry_orig_err_msg = dict()
    # Map notebooks that need to be retried to the theory whose common
    # expression notebook must be executed first:
    retry_prerequisite = dict()
    # retry_prerequisite values that have not been satisfied:
    unmet_prerequisites = set()
    # ranks that have been assigned to execute a notebook but
    # haven't finished.
    unfinished_ranks = set()
    # Set of theories for which a notebook was successfully executed:
    successful_execution_theories = set()

    # Inner functions to address retrying notebooks when executing
    # common expression notebooks and one imports from another that
    # hasn't been executed yet.
    def generate_notebook_paths_with_retries():
        # Try all of the notebooks once.
        while True:
            try:
                yield next(notebook_paths)
            except StopIteration:
                break
        # Retry some of the notebooks as needed and/or
        # wait for unfinished notebooks.
        while len(retry_notebooks) > 0 or len(unfinished_ranks) > 0:
            # print(len(retry_notebooks), 'retries', len(unfinished_ranks),
            #      'unfinished', len(unmet_prerequisites), 'unmet_prerequisites')
            yielded_retry = False
            if len(retry_notebooks) > 0:
                for to_retry in retry_notebooks:
                    retry_theory_name = retry_notebook_to_theory_name[to_retry]
                    prerequisite = retry_prerequisite[retry_theory_name]
                    if prerequisite in unmet_prerequisites:
                        if (prerequisite not in retry_prerequisite.keys() and
                                len(unfinished_ranks) == 0):
                            # Unable to satisfy the prerequisite because
                            # it isn't queued up.
                            raise Exception("Error while executing %s\n%s" % (
                                to_retry, retry_orig_err_msg[to_retry]))
                    else:
                        retry_notebooks.remove(to_retry)
                        yield to_retry
                        yielded_retry = True
                        break
            if not yielded_retry:
                # We have to wait for unfinished notebooks.
                yield None

    def should_retry_after_failed_execution(notebook_path, orig_err_msg):
        common_notebook_name = 'common.ipynb'
        if notebook_path[-len(common_notebook_name):] != common_notebook_name:
            # Only retry for common expression notebooks.
            return False
        theory = Theory(notebook_path)
        import_failure_filename = os.path.join(
            theory._theory_folder_storage('common').path,
            'import_failure.txt')
        if os.path.isfile(import_failure_filename):
            # There was a failure to import a common expression from
            # a different theory, so we should try again.
            retry_notebooks.add(notebook_path)
            retry_notebook_to_theory_name[notebook_path] = theory.name
            with open(import_failure_filename, 'r') as f:
                failed_import = f.read().strip()
            retry_prerequisite[theory.name] = failed_import
            if (failed_import in retry_prerequisite and
                    retry_prerequisite[failed_import] == theory.name):
                raise Exception("Cyclic dependency between %s and %s common "
                                "expression notebooks detected" %
                                (failed_import, theory.name))
            retry_orig_err_msg[notebook_path] = orig_err_msg
            if failed_import not in successful_execution_theories:
                # Note: the prerequisite may have been satisfied
                # while this was being executed; that's why we
                # track the 'successful_execution_theories'.
                unmet_prerequisites.add(failed_import)
            return True
        else:
            return False
    count = 0

    def successful_execution_notification(notebook_path):
        nonlocal count
        count += 1
        common_filename = 'common.ipynb'
        if notebook_path[-len(common_filename):] == common_filename:
            theory = Theory(notebook_path)
            successful_execution_theories.add(theory.name)
            unmet_prerequisites.discard(theory.name)
    
    if nranks == 1:
        # The boring single rank case.
        with RecyclingExecutePreprocessor(kernel_name='python3', timeout=-1) as execute_processor:
            for notebook_path in generate_notebook_paths_with_retries():
                try:
                    execute_and_maybe_export_notebook(
                        execute_processor, notebook_path, no_latex=no_latex,
                        no_execute=no_execute, git_clear=git_clear,
                        export_to_html=export_to_html)
                    successful_execution_notification(notebook_path)
                except Exception as e:
                    if not should_retry_after_failed_execution(notebook_path,
                                                               str(e)):
                        raise e
    elif rank > 0:
        # These ranks will request assignments from rank 0
        try:
            with RecyclingExecutePreprocessor(kernel_name='python3', timeout=-1) as execute_processor:
                comm.send(rank, dest=0)
                while True:
                    notebook_path = comm.recv(source=0)
                    if len(notebook_path) == 0:
                        break  # empty path is "done" signal
                    try:
                        execute_and_maybe_export_notebook(
                            execute_processor, notebook_path, no_latex=no_latex,
                            no_execute=no_execute, git_clear=False,
                            export_to_html=export_to_html)
                        comm.send(rank, dest=0)
                    except Exception as e:
                        comm.send((rank, str(e)), dest=0)
        except KernelStart_failure:
            # Occassionally there is an error getting a Jupyter notebook
            # engine started.  If that happens, just this this one out
            # and let the other cores keep going.
            print(
                "Kernel failed to start on rank %d.  Going on without this rank." %
                rank)
            pass
    else:
        # Send out assignments as they are requested.
        assignments = [None] * nranks  # remember the assigments of the ranks.

        def process_response(msg):
            # Checks for an error message in the response from the
            # worker ranks; otherwise, it will be the rank itself.
            try:
                ready_rank = int(msg)
            except TypeError:
                # If we get anything other than an integer,
                # it must be an exception message.
                err_rank = int(msg[0])
                failed_notebook = assignments[err_rank]
                if not should_retry_after_failed_execution(failed_notebook,
                                                           msg[1]):
                    print("Error while executing %s:" % failed_notebook)
                    print(msg[1])
                    comm.Abort()
                else:
                    print("\tFailure to execute %s, but we may retry "
                          "after satisfying prerequisites" % failed_notebook)
                return err_rank
            finished_notebook = assignments[ready_rank]
            if finished_notebook is not None:
                successful_execution_notification(finished_notebook)
                if git_clear:
                    git_clear_notebook(finished_notebook)
            return ready_rank
        try:
            idle_ranks = set()
            for notebook_path in generate_notebook_paths_with_retries():
                if notebook_path is not None and len(idle_ranks) > 0:
                    # Send the job to a rank that was sitting idle.
                    ready_rank = idle_ranks.pop()
                else:
                    # Wait for a request/response from one of the ranks.
                    ready_rank = process_response(
                        comm.recv(source=MPI.ANY_SOURCE))
                if notebook_path is not None:
                    unfinished_ranks.add(ready_rank)
                    comm.send(notebook_path, ready_rank)
                else:
                    unfinished_ranks.discard(ready_rank)
                    idle_ranks.add(ready_rank)
                assignments[ready_rank] = notebook_path
        except Exception as e:
            print(str(e))
            comm.Abort()
        # And now we are done
        for dest in range(1, nranks):
            comm.send("", dest)
    if rank == 0:
        print("Finished executing %d notebooks" % count)


def notebook_path_generator(top_level_paths, notebook_filename):
    for path in top_level_paths:
        for theory_path in find_theory_paths(path):
            yield os.path.join(theory_path, notebook_filename)


def theoremproof_path_generator(top_level_paths):
    for path in top_level_paths:
        for theory_path in find_theory_paths(path):
            theory = Theory(theory_path)
            for theorem_name in theory.get_theorem_names():
                yield os.path.join(theory._storage.directory, '_theory_nbs_',
                                   'proofs', theorem_name, 'thm_proof.ipynb')


def database_notebook_path_generator(top_level_paths, filebases):
    for path in top_level_paths:
        for theory_path in find_theory_paths(path):
            pv_it_dir = os.path.join(theory_path, '__pv_it')
            if os.path.isdir(pv_it_dir):
                for folder in os.listdir(pv_it_dir):
                    folder_dir = os.path.join(pv_it_dir, folder)
                    if os.path.isdir(folder_dir):
                        for hash_directory in os.listdir(folder_dir):
                            hash_path = os.path.join(
                                folder_dir, hash_directory)
                            if os.path.isdir(hash_path):
                                # if hash_path in executed_hash_paths:
                                #    continue # already executed this case
                                for filebase in filebases:
                                    notebook_path = os.path.join(
                                        hash_path, filebase + '.ipynb')
                                    if os.path.isfile(notebook_path):
                                        yield notebook_path

                                    """
                                        html_path = os.path.join(hash_path, filebase+'.html')
                                        notebook_path = os.path.join(hash_path, filebase+'.ipynb')
                                        if os.path.isfile(notebook_path):
                                            if no_execute:
                                                export_notebook_to_html(notebook_path)
                                            else:
                                                # if expr_html doesn't exist or is older than expr_notebook, generate it
                                                if not os.path.isfile(html_path) or os.path.getmtime(html_path) < os.path.getmtime(notebook_path):
                                                    # execute the expr.ipynb notebook
                                                    execute_and_export_notebook(
                                                            execute_processor,
                                                            notebook_path,
                                                            no_latex=no_latex, git_clear=False)
                                                    executed_hash_paths.add(hash_path) # done
                                    # always execute the dependencies notebook for now to be safes
                                    dependencies_notebook = os.path.join(hash_path, 'dependencies.ipynb')
                                    if os.path.isfile(dependencies_notebook):
                                        # execute the dependencies.ipynb notebook
                                        execute_and_export_notebook(
                                                execute_processor, dependencies_notebook,
                                                no_execute=no_execute, no_latex=no_latex,
                                                git_clear=False)
                                    """

if __name__ == '__main__':
    if os.path.sep != '/':
        # use the appropriate path separator for the OS
        default_paths = [path.replace('/', os.path.sep)
                         for path in default_paths]

    # parse the arguments and provide help information.
    parser = argparse.ArgumentParser(
        description=('Build all of the Prove-It notebooks in selected '
                     'directories.  Works with mulptiple processors via '
                     'mpi4py (e.g., using mpirun).'))
    parser.add_argument(
        '--clean',
        dest='clean',
        action='store_const',
        const=True,
        default=False,
        help='remove all of the autogenerated __pv_it directories')
    parser.add_argument(
        '--download',
        dest='download',
        action='store_const',
        const=True,
        default=False,
        help=("download and extract the tarball of __pv_it directories from "
              "the 'master-full' branch with some limitations (skipping "
              "notebooks with non-empty corresponding 'git diff' output)"))
    parser.add_argument(
        '--extract',
        dest='tar',
        type=str,
        default="",
        help=("extract (with the same limitations as with --download) "
              "from the specified tar file"))
    parser.add_argument(
        '--essential',
        dest='build_essential',
        action='store_const',
        const=True,
        default=True,
        help=('build the notebooks that define the common expressions, axioms, '
              'and theorems of the theories, essential for interdependencies '
              '(default if no other selections are made).'))
    parser.add_argument(
        '--all',
        dest='build_all',
        action='store_const',
        const=True,
        default=False,
        help=('build all of the notebooks in the supplied paths in a '
              'particular order (i.e. building the entire proveit website).'))
    parser.add_argument(
        '--theories',
        dest='build_theories',
        action='store_const',
        const=True,
        default=False,
        help=('build the _theory_ notebook for each theory '
              '(--essential is disabled)'))
    parser.add_argument(
        '--commons',
        dest='build_commons',
        action='store_const',
        const=True,
        default=False,
        help=("build the 'common' notebooks for common expressions of "
              "each theory (--essential is disabled)"))
    parser.add_argument(
        '--axioms',
        dest='build_axioms',
        action='store_const',
        const=True,
        default=False,
        help=("build the 'axioms' notebooks defining theory axioms "
              "(also update 'theory' notebooks, --essential is disabled)"))
    parser.add_argument(
        '--theorems',
        dest='build_theorems',
        action='store_const',
        const=True,
        default=False,
        help=("build the 'theorems' notebooks defining theory theorems "
              "(also update 'theory' notebooks, --essential is disabled)"))
    parser.add_argument(
        '--demos',
        dest='build_demos',
        action='store_const',
        const=True,
        default=False,
        help=("build the 'demonstrations' notebook for each theory and "
              "other extraneous notebooks, like tutorials "
              "(--essential is disabled)"))
    parser.add_argument(
        '--theorem_proofs',
        dest='build_theorem_proofs',
        action='store_const',
        const=True,
        default=False,
        help=("build the 'thm_proof' notebook for each theorem "
              "(also update 'theorems' notebooks --essential is disabled)"))
    parser.add_argument(
        '--dependencies',
        dest='build_dependencies',
        action='store_const',
        const=True,
        default=False,
        help=('build the _dependencies_ notebooks corresponding with '
              'theorem proofs (--essential is disabled)'))
    parser.add_argument(
        '--expr_and_proofs',
        dest='build_expr_and_proofs',
        action='store_const',
        const=True,
        default=False,
        help=('build expression and proof notebooks, including sub-expressions '
              'and sub-proofs (--essential is disabled)'))
    parser.add_argument('--nolatex', dest='nolatex', action='store_const',
                        const=True, default=False,
                        help='speed execution by skipping LaTeX generation')
    parser.add_argument('--noexecute', dest='noexecute', action='store_const',
                        const=True, default=False,
                        help='do not execute notebooks, just convert to HTML')
    parser.add_argument(
        '--nogitclear',
        dest='nogitclear',
        action='store_const',
        const=True,
        default=False,
        help='do not bother doing "git add" to clear git of notebooks whose modifications are only in filtered output')
    parser.add_argument(
        '--nohtml',
        dest='nohtml',
        action='store_const',
        const=True,
        default=False,
        help='do not export notebooks to HTML, just execute them')
    parser.add_argument(
        'path',
        type=str,
        nargs='*',
        default=default_paths,
        help='paths to be processed; sub-theories will be included recursively (default: %s)' %
        ' '.join(default_paths))
    args = parser.parse_args()
    paths = args.path

    # Get all the theories of the given top-level paths
    # in the order indicated in _sub_theory_.txt files.
    theory_paths = []
    theory_map = dict()  # map Theory names to paths
    for path in paths:
        for theory_path in find_theory_paths(path):
            theory_paths.append(theory_path)
            theory_map[Theory(theory_path).name] = theory_path

    all_paths = list(theory_paths)
    all_paths += [path for path in paths if path not in theory_paths]
    
    # Use mpi for parallel processing if desired and possible.
    try:
        from mpi4py import MPI
        comm = MPI.COMM_WORLD
        rank = comm.Get_rank()
        nranks = comm.Get_size()
    except BaseException:
        rank, nranks = 0, 1

    if args.clean:
        # clean all of the __pv_it directories that may be auto-generated
        print("Cleaning '__pv_it' directories...")
        sys.stdout.flush()
        for path in all_paths:
            pv_it_dir = os.path.join(path, '__pv_it')
            os.system('rm -fr "%s"'%pv_it_dir)
            '''
            # remove files from __pv_it folders except *.png, *.latex kinds.
            for sub in os.listdir(pv_it_dir):
                if sub == '_referenced_':
                    shutil.rmtree(os.path.join(pv_it_dir, '_referenced_'))
                    continue
                sub_path = os.path.join(pv_it_dir, sub)
                if os.path.isdir(sub_path):
                    for _sub in os.listdir(sub_path):
                        if _sub[-4:] == '.png': continue
                        if _sub[-6:] == '.latex': continue
                        else:
                            os.remove(os.path.join(sub_path, _sub))
                else:
                    os.remove(sub_path)
            '''
    elif not args.download and args.tar == '':
        if (args.build_commons or args.build_axioms or args.build_theorems or 
                args.build_theories or args.build_demos or args.build_theorem_proofs or
                args.build_dependencies or args.build_expr_and_proofs):
            # Disable --essential if anything more specific is requested.
            args.build_essential = False
        if args.build_commons or args.build_all or args.build_essential:
            if rank == 0:
                # First remove the __pv_it/common/name_to_hash.txt files to make
                # sure we are using the correct version of the common expressions.
                for path in paths:
                    for theory_path in find_theory_paths(path):
                        name_to_hash_filename = os.path.join(
                            theory_path, '__pv_it', 'common', 'name_to_hash.txt')
                        if os.path.isfile(name_to_hash_filename):
                            os.remove(name_to_hash_filename)
            if nranks > 1:
                comm.barrier()

            mpi_build(notebook_path_generator(paths, '_theory_nbs_/common.ipynb'),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
        if args.build_axioms or args.build_all or args.build_essential:
            mpi_build(notebook_path_generator(paths, '_theory_nbs_/axioms.ipynb'),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
        if args.build_theorems or args.build_all or args.build_essential:
            mpi_build(notebook_path_generator(paths, '_theory_nbs_/theorems.ipynb'),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
        if (args.build_theories or args.build_axioms or args.build_theorems
                or args.build_all or args.build_essential):
            # Update the theory after updating axioms/theorems so all the
            # theory information is up-to-date.  Also include index.ipynb
            # (which should update with updates to theories) and guide.ipynb
            # (because somebody has to).
            theory_nb_gen = notebook_path_generator(paths, '_theory_nbs_/theory.ipynb')
            mpi_build(itertools.chain(theory_nb_gen, ('index.ipynb', 'guide.ipynb')),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
        if args.build_demos or args.build_all:
            # Build demonstration and 'extra' notebooks.
            def extra_notebook_gen():
                '''
                Yield 'extra' notebooks (not in '_theory_nbs' folders).
                '''
                for main_path in paths:
                    for _k, path in enumerate(itertools.chain(
                            [main_path], find_theory_paths(main_path))):
                        if _k > 0 and path==main_path:
                            continue # avoid visiting main_path twice.
                        for sub_path in os.listdir(path):
                            full_path = os.path.join(path, sub_path)
                            if sub_path[0] == '_':
                                # skip notebook with preceeding underscore.
                                continue
                            if (sub_path[-6:] == '.ipynb' and os.path.isfile(full_path)):
                                yield full_path
            notebook_paths = itertools.chain(
                notebook_path_generator(paths, '_theory_nbs_/demonstrations.ipynb'),
                extra_notebook_gen())
            mpi_build(notebook_paths,
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
                            
        if args.build_theorem_proofs or args.build_all:
            mpi_build(theoremproof_path_generator(paths),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
            # Rebuild the theorem notebooks after the theorem proofs
            # so they will indicate an updated status of theorems.
            mpi_build(notebook_path_generator(paths, '_theory_nbs_/theorems.ipynb'),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)

        # This seems to be necessary to rerun these after rerunning the
        # theorem notebooks, though it shouldn't be.  Why?
        if args.build_demos or args.build_all:
            mpi_build(notebook_path_generator(paths, '_theory_nbs_/demonstrations.ipynb'),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
        if args.build_theorem_proofs or args.build_all:
            mpi_build(theoremproof_path_generator(paths),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)


        if args.build_dependencies or args.build_all:
            mpi_build(database_notebook_path_generator(paths, ('dependencies',)),
                      no_latex=args.nolatex, git_clear=not args.nogitclear,
                      no_execute=args.noexecute, export_to_html=True)
        if args.build_expr_and_proofs or args.build_all:
            filebases = ('expr', 'common_expr', 'axiom_expr', 'theorem_expr', 'proof')
            mpi_build(database_notebook_path_generator(paths, filebases),
                      no_latex=args.nolatex, git_clear=False,
                      no_execute=args.noexecute, export_to_html=True)


    tar_file = args.tar
    if args.download:
        '''
        Download and extract the tarball of __pv_it directories as well
        as notebook outputs and html versions.
        '''
        url = ("https://github.com/sandialabs/Prove-It/archive/"
               "gh-pages.tar.gz")
        if rank == 0:
            if not sure_you_want_to_extract(paths):
                print('Quitting')
                tar_file = ''
            else:
                print("Downloading '%s'" % url)
                try:
                    tar_file = urllib.request.urlretrieve(
                        url, filename=None)[0]  # Comment in for Python 3
                except urllib.error.URLError as e:
                    print(str(e))
                    raise Exception(
                        "Unable to download %s; there may be a firewall "
                        "issue.\nIn any case, you can try downloading this "
                        "file manually and then use '--extract'."%url)        
    elif tar_file != "":
        if rank == 0 and not sure_you_want_to_extract(paths):
            print('Quitting')
            tar_file = ''
    if nranks > 1:
        tar_file = comm.bcast(tar_file, root=0)
    if tar_file != "":
        extract_tar_with_limitations(tar_file, paths)
        #extract_tar_test(tar_file, paths)
        
