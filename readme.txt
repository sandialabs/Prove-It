Welcome to Prove-It!

Prove-It is a tool for proving and organizing general theorems using Python.

Prove-It uses a powerful yet simple approach to theorem-proving.  
It is not designed with automation as the primary goal.  The primary goal is 
flexibility in order to be able to follow, ideally, any valid and complete 
(indivisible) chain of reasoning.  To that end, users can write additional 
Python scripts to make their own mathematical operations and LaTeX formatting 
rules.  Axioms are statements that are taken to be true without proof.  They
can be added by the user at will in order to define their new mathematical 
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
theorem dependencies are stored in a kind of database (filesystem based).  This
database is used to prevent circular logic. It also allows users to track 
axioms and unproven theorems required by any particular proof.  Convenience
methods and automation tools may be added which utilize new theorems and aid
future proofs.  Mathematical objects and operations, axioms, and theorems 
are organized into built-in and user-defined packages.  

Visit http://pyproveit.org to view the Prove-It generated web pages.

******************************************************************************************
Installation instructions

1) Make sure you have the required packages installed:
    - Python3.7 (installing a distribution such as Anaconda is recommended)
    - Jupyter (included in a distribution such as Anaconda)
    - LaTeX distribution (e.g. MiKTeX or TeX Live)

2) Run:

   python setup.py develop
   
   to install a link to the source tree in your python path, so that changes you make to 
   the code are immediately updated when Prove-It is imported.  This is recommended if
   you plan to make updates/additions to the ever-expanding proveit packages.
   Alternatively, run:
   
   python setup.py install 

   if you wish to install Prove-It into your main python distribution without
   doing any development on the proveit packages.
   
3) Run:

   python build.py --clean --download
   
   to download and extract the Prove-It "database" files distributed in "__pv_it"
   folders throughout the Prove-It sub-folders.  The "--clean" option will erase
   anything that may have been added to your local database before extracting
   the downloaded version.
      
4) Take a look at the "tutorial" folder.  It has numbered Juptyer notebooks 
   (and html versions for convenience) that introduce Prove-It concepts
   in an appropriate order.  There are also tutorial notebooks/html in various
   packages with specific information about that package.  A particularly
   useful one is "proveit/logic/equality/equality_tutorial.ipynb" in the
   "packages" folder.  Furthermore, there are "_proofs_" folders in various
   packages with Jupyter notebooks that prove theorems of the package.  You
   can peek at these for examples of how Prove-It works in practice.  Note that 
   "proofs" folders, without the underscores, are outdated proofs that will
   likely fail to execute.

5) It is intended that packages continue to be added and updated to cover
   an ever-expanding range of mathematical knowledge.  Packages may have
   cross dependencies (as long as there is no circular reasoning in any
   particular proof).  Classes/objects that should be accessible externally
   should be imported in the __init__.py of the top-level package, and they
   should be accessed, externally, at this top level.  For example, the
   "Or" class is contained in "proveit.logic.boolean.disjunction.or_op.py" but
   it can and should be accessed via "from proveit.logic import Or".
   In this way, the sub-package structure can be useful for organization 
   purposes without being cumbersome to the user.  Here is the current list
   of top-level packages under development, with brief descriptions:
   
    _core_: Core Prove-It constructs required used to construct/verify proofs.
    logic: Boolean arithmetic, equality, and set theory.
    number: Arithmetic and number theory concepts.
    relations: Some generic routines for search/sorting among transitive 
               relationships.
    trigonometry: A few things pertaining to trigonometry.
    linalg: A few things pertaining to linear algebra.
    statistics: A few things pertaining to statistics.
    physics: Currently just things related to proving the correctness of the
             Quantum Phase Estimation algorithm at an abstract level.
             (this was implemented in an older version of Prove-It; redoing
             it more properly in the current version is in progress.)


******************************************************************************************
Version history

12 Feb. 2017 
    - Moved repository to github.com/PyProveIt/Prove-It.
12 Jan. 2017 - v0.3 
    - The code is now hosted on gitlab-ex.sandia.gov to make it accessible to
      collaborators.
******************************************************************************************

