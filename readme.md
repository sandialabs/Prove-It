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

       python build.py --clean --download
   
   to download and extract the Prove-It "database" files distributed in
   `__pv_it` folders throughout the Prove-It sub-folders.  The `--clean`
   option will erase anything that may have been added to your local
   database before extracting the downloaded version.

4) It is intended that theory packages continue to be added and updated 
   to cover an ever-expanding range of mathematical knowledge.  Theory 
   packages may have cross dependencies (as long as there is no circular
   reasoning in any particular proof).  Classes/objects that should be 
   accessible externally should be imported in the `__init__.py` file
   of the top-level package, and they should be accessed, externally,
   at this top level.  For example, the `Or` class is contained in the
   python file

   `proveit.logic.boolean.disjunction.or_op.py`

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
      <td style="font-family:courier, courier new;">logic</td>
      <td>Boolean arithmetic, equality, and set theory.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">number</td>
      <td>Arithmetic and number theory concepts.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new; vertical-align:top;">relations</td>
      <td>Some generic routines for search/sorting among transitive 
               relationships.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">trigonometry</td>
      <td>A few things pertaining to trigonometry.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">linalg</td>
      <td>A few things pertaining to linear algebra.</td>
    </tr>
    <tr>
      <td style="font-family:courier, courier new;">statistics</td>
      <td>A few things pertaining to statistics.</td>
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

5) Take a look at the `tutorial` folder.  It has numbered Jupyter notebooks 
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

