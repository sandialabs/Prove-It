# Welcome to Prove-It!

<font size="3">
Prove-It is a tool for proving and organizing general theorems using
Python.

Prove-It uses a powerful yet simple approach to theorem-proving.

Prove-It is not designed with automation as the _primary_ goal.
The primary goal is 
flexibility in order to be able to follow, ideally, any valid and complete 
(indivisible) chain of reasoning.

To that end, users can write additional Python scripts to make their own
mathematical operations and LaTeX formatting rules. Axioms are statements
that are taken to be true without proof.  They can be added by the user
at will in order to define their new mathematical 
objects and operations.  Users can also add theorems that are to be proven.
Theorems may be proven in any order.  Theorem proofs are constructed in 
Jupyter notebooks (interactive Python sessions in a web browser).  These 
notebooks render LaTeX-formatted mathematical expressions inline.  Proofs 
are constructed by invoking axioms and other theorems and employing 
fundamental derivation steps (modus ponens, hypothetical reasoning, 
specialization, generalization, or axiom elimination).  Axioms and theorems
may be invoked indirectly via convenience methods or automation (methods
that are automatically invoked when attempting to prove something or as
side-effects when something is proven).  Theorem proofs and their axiom/
theorem dependencies are stored in a kind of database (filesystem based).
This database is used to prevent circular logic. It also allows users to
track axioms and unproven theorems required by any particular proof.
Convenience methods and automation tools to aid future proofs may be 
added and may utilize new axioms/theorems.  Mathematical objects and operations,
axioms, and theorems are organized into built-in and user-defined 
theory packages. 

Visit [http://pyproveit.org](http://pyproveit.org) to view the
Prove-It-generated web pages.  
You can also read our [introductory paper](https://github.com/PyProveIt/Prove-It/blob/master/ProveIt_Introduction.pdf).

<br/>

***

Installation instructions

1) Make sure you have the required packages installed:
    - Python3.7 (installing a distribution such as Anaconda is recommended)
    - Jupyter (included in a distribution such as Anaconda)
    - LaTeX distribution (e.g. MiKTeX or TeX Live)
    - The qcircuit LaTeX package which may be acquired from CTAN
      (or disable the quantum theory package in Prove-It).

2) Run:

       python setup.py develop
   
   to install a link to the source tree in your python path.  We only
   support this "develop" installation at this time because of the way 
   that the Prove-It database works in the filesystem.  In any case, if 
   you might want to make any [contributions](https://github.com/PyProveIt/Prove-It/blob/master/CONTRIBUTING.md)
   to the ever-expanding proveit packages, this "develop" installation will
   allow you to do that development (altering source code of the
   installed package).
   
3) Run:

       python build.py --essential
   
   to execute Jupyter notebooks that will define axioms and theorems
   of each theory package as well as commonly used expressions.  You will
   then be able to execute any notebook in the system as well as experiment
   on your own.  Currently, this takes about 10 minutes on a single core.
   Use the "--help" option to see other "build" options (for example,
   `python build.py --download` will essentially download the entire 
   contents of the `pyproveit.org` website).
   It is also possible to execute the `build.py` script using multiple
   cores with mpi4py.  For example, if you have 4 cores available in
   your system and mpi/mpi4py is installed, 
   `mpirun -np 4 build.py --essential` will
   build the essential theory package notebooks using 3 active cores 
   (one core will assign tasks to the other three).
   
   To disable the quantum physics package (and alleviate the need to install
   the qcircuit LaTeX package), remove "quantum" from 
   `packages/proveit/physics/_sub_theories_.txt`.

4) It is intended that theory packages continue to be added and updated 
   to cover an ever-expanding range of mathematical knowledge.  Theory 
   packages may have cross dependencies (as long as there is no circular
   reasoning in any particular proof).  Classes/objects that should be 
   accessible externally should be imported in the `__init__.py` file
   of the top-level package, and they should be accessed, externally,
   at this top level.  For example, the `Or` class is contained in the
   python file

   `proveit.logic.booleans.disjunction.or_op.py`

   but it can and should be accessed via the import command

       from proveit.logic import Or 
   
   In this way, the sub-package structure can be useful for organization 
   purposes without being cumbersome to the user.

   Here is the current list
   of top-level packages under development, with brief descriptions:
   
   <table style="padding:10px; border: 1px solid black; font-size: 100%;"
          cellpadding="5" width="75%">
    <tr>
      <td style="font-family:courier, courier new;">_core_</td>
      <td>Core Prove-It constructs required used to construct/verify
            proofs.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">_core_expr_types_</td>
      <td>Theory package with axioms/theorems pertaining to some of the core expression types.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">logic</td>
      <td>Theory package for boolean arithmetic, equality, and set theory.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">numbers</td>
      <td>Theory package for arithmetic and number theory concepts.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new; vertical-align:top;">relations</td>
      <td>Some generic routines for search/sorting among transitive 
               relationships.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">trigonometry</td>
      <td>Yet to be a theory package pertaining to trigonometry.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">linalg</td>
      <td>Yet to be a theory package pertaining to linear algebra.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">statistics</td>
      <td>Yet to be a theory package pertaining to statistics.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new; vertical-align:top;"
      valign="top">physics</td>
      <td>Currently just things related to proving the correctness of
          the Quantum Phase Estimation algorithm at an abstract level.
          (This was implemented in an older version of Prove-It;
          redoing it more properly in the current version is in
          progress.)</td>
    </tr>
   </table>

5) The tutorial notebooks in the `tutorial` folder are in progress.  
   It has numbered Jupyter notebooks 
   (and html versions for convenience) that introduce Prove-It concepts
   in an appropriate order.  There are also "demonstration" notebooks/html
   in the various theory packages with specific information about that
   package.  A particularly useful one is

   `proveit/logic/equality/_demonstrations_.ipynb`
   
   You can also look at existing proofs for examples.  Each theory
   package has a `_theorems_.ipynb` notebook.  The theory name hyperlinks
   to a proof notebook for that theorem which may or may not be complete.
   Note that Prove-It allows "unproven theorems" to be used as "conjectures",
   so some useful theorems exist without being proven as the system continues
   to develop.

<br/>

***

<table style="padding:15px; border: 1px solid black; font-size:80%;" cellpadding="5">
<tr>
  <td style="font-weight: bold" colspan="2">Version History</td>
</tr>
<tr>
  <td style="width:auto;white-space: nowrap" valign="top">
    12 Feb. 2017
  </td>
  <td>
    Moved repository to github.com/PyProveIt/Prove-It.
  </td>
</tr>
<tr>
  <td style="width:auto;white-space: nowrap;" valign="top">
    12 Jan. 2017 - v0.3
  </td>
  <td>
    The code is now hosted on gitlab-ex.sandia.gov to make it accessible
    to collaborators.
  </td>
</tr>
</table>

