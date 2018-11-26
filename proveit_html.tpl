{%- extends 'basic.tpl' -%}


{%- block header -%}
<!DOCTYPE html>
<html>
<head>
{%- block html_head -%}
<meta charset="utf-8" />
<title>{{ resources['title'] }}</title>

<style type="text/css">
/* Overrides of notebook CSS for static HTML export */
body {
  overflow: visible;
  padding: 8px;
}
div#notebook {
  overflow: visible;
  border-top: none;
}
{%- if resources.global_content_filter.no_prompt-%}
div#notebook-container{
  padding: 6ex 12ex 8ex 12ex;
}
{%- endif -%}
@media print {
  div.cell {
    display: block;
    page-break-inside: avoid;
  } 
  div.output_wrapper { 
    display: block;
    page-break-inside: avoid; 
  }
  div.output { 
    display: block;
    page-break-inside: avoid; 
  }
}
</style>

<!-- Custom stylesheet, it must be in the same directory as the html file -->
<link rel="stylesheet" href="notebook.css">

<script type="text/x-mathjax-config">
MathJax.Hub.Config({
  tex2jax: {inlineMath: [['$','$'], ['\\(','\\)']]}
});
</script>
<script type="text/javascript" async
  src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.5/latest.js?config=TeX-MML-AM_CHTML">
</script>

{%- endblock html_head -%}
</head>
{%- endblock header -%}

{% block body %}
<body>
  <div tabindex="-1" id="notebook" class="border-box-sizing">
    <div class="container" id="notebook-container">
{{ super() }}
    </div>
  </div>
<footer>
  <p>These web pages were generated on {{ resources['today'] }} by <a href="https://github.com/PyProveIt/Prove-It">Prove-It</a> Beta Version 0.3, licensed under the GNU Public License by Sandia Corporation.</p>
  <p>Presented proofs are not absolutely guaranteed.  For assurance, it is important to check the structure 
  of the statement being proven, independently verify the derivation steps, track dependencies, and ensure that 
  employed axioms are valid and properly structured.  Inconsistencies may exist, unknowingly, in this system.
  </p>
  <p>
  This material is based upon work supported by the U.S. Department of Energy, Office of Science, Office of Advanced Scientific Computing Research, under the Quantum Computing Application Teams program. Sandia National Labs is managed and operated by National Technology and Engineering Solutions of Sandia, LLC, a subsidiary of Honeywell International, Inc., for the U.S. Dept. of Energy's NNSA under contract DE-NA0003525. The views expressed above do not necessarily represent the views of the DOE or the U.S. Government.
  </p>
  <br>
  <p>Please send questions/comments to: <a href="mailto:wwitzel@sandia.gov">
  wwitzel@sandia.gov</a>.</p>
</footer> 
</body>
{%- endblock body %}

{% block footer %}
{{ super() }}
</html>
{% endblock footer %}