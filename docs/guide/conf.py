# pylint: disable=C0103,C0114,C0116,C0301,E0402,W0622
#
# Configuration file for Verilator's Sphinx documentation builder.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#
# This file only contains overridden options. For a full list:
# https://www.sphinx-doc.org/en/master/usage/configuration.html
#
# ----------------------------------------------------------------------
# -- Path setup

from datetime import datetime
import os
import re
import sys
sys.path.insert(0, os.path.abspath('./_ext'))

import sphinx_rtd_theme  # pylint: disable=wrong-import-position,


def get_vlt_version():
    filename = "../../Makefile"
    with open(filename) as fh:
        for line in fh:
            match = re.search(r"PACKAGE_VERSION_NUMBER *= *([a-z0-9.]+)", line)
            if match:
                return match.group(1)
    return "unknown"


def setup(app):
    app.add_css_file('css/vlt_sphinx.css')


# ----------------------------------------------------------------------
# -- Project information

project = 'Verilator'
copyright = '2022 by Wilson Snyder, under LGPL-3.0 or Artistic-2.0'
author = 'Wilson Snyder'

# The master toctree document.
master_doc = "index"

version = get_vlt_version()
release = get_vlt_version()

rst_prolog = """
.. role:: vlopt(option)
"""

# ----------------------------------------------------------------------
# -- General configuration

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
# To install:
#   sudo install enchant
#   sudo pip3 install sphinx sphinx_rtd_theme breathe sphinxcontrib-spelling
# We keep this list empty for now to avoid needing dependencies
extensions = []
# extensions = ['breathe', 'sphinxcontrib.spelling']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = [
    '_build', 'Thumbs.db', '.DS_Store', 'internals.rst', 'xml.rst', 'gen/ex_*',
    'CONTRIBUTING.rst'
]

# Warn about refs
nitpicky = True
nitpicky_ignore = []

# Number figures for referencing
numfig = True

# The name of the Pygments (syntax highlighting) style to use.
pygments_style = "sphinx"

# The suffix(es) of source filenames.
# You can specify multiple suffix as a list of string:
source_suffix = [".rst"]

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# Date format to ISO
today_fmt = datetime.now().strftime("%F")

# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = True

# Could use this for internals<->guide references
# intersphinx_mapping = { 'sphinx': ('https://sphinx-doc.org/', None), }

# ----------------------------------------------------------------------
# -- Options for HTML output

# html_baseurl =

html_domain_indices = False

html_logo = "../_static/verilator_192_150_min.png"

html_theme = 'sphinx_rtd_theme'
html_theme_path = [sphinx_rtd_theme.get_html_theme_path()]

html_theme_options = {
    'analytics_id': 'G-D27B0C9QEB',
    'logo_only': True,
    'style_nav_header_background': "#45acf8",  # Default is #2980B9
    # 'canonical_url':
}

html_context = {
    'display_github': True,
    'github_user': 'verilator',
    'github_repo': 'verilator',
    'github_version': 'master/docs/guide/',
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['../_static']

# If true, "Created using Sphinx" is shown in the HTML footer. Default is True.
html_show_sphinx = False

html_copy_source = False
html_show_sourcelink = False

html_use_index = False

html_favicon = "../_static/verilator_32x32_min.png"

# Custom sidebar templates, maps document names to template names.
# html_sidebars

# Add any extra paths that contain custom files (such as robots.txt or
# .htaccess) here, relative to this directory. These files are copied
# directly to the root of the documentation.
# html_extra_path = []

# Additional templates that should be rendered to pages, maps page names to
# template names.
# html_additional_pages = {}

# ----------------------------------------------------------------------
# -- Options for Latex output

latex_logo = "../_static/verilator_logo.png"

latex_elements = {
    'extraclassoptions': 'openany,oneside',
    'papersize': 'letterpaper',
    'makeindex': '',
    'printindex': '',
    # 'pointsize': '10pt',
    # 'preamble': '',
}

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
# latex_documents = [
#    (
#        master_doc,
#        "Verilog-to-Routing.tex",
#        "Verilog-to-Routing Documentation",
#        "VTR Developers",
#        "manual",
#    ),
# ]

# For "manual" documents, if this is true, then toplevel headings are parts,
# not chapters.
# latex_use_parts = False

# If true, show page references after internal links.
# latex_show_pagerefs = False

# If true, show URL addresses after external links.
# latex_show_urls = False

latex_domain_indices = False

# ----------------------------------------------------------------------
# -- Options for manual page output

# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
# man_pages = [(master_doc, "verilog-to-routing", "Verilog-to-Routing Documentation", [author], 1)]

# If true, show URL addresses after external links.
# man_show_urls = False

# ----------------------------------------------------------------------
# -- Options for spelling

spelling_word_list_filename = ['spelling.txt']
spelling_ignore_contributor_names = True

# ----------------------------------------------------------------------
# -- Options for doxygen

# if shutil.which("doxygen"):
#    breathe_projects = {
#        "verilated": "../_build/doxygen/verilated/xml",
#    }
#    breathe_default_project = "verilated"
#
#    if not os.environ.get("SKIP_DOXYGEN", None) == "True":
#        for prjname, prjdir in breathe_projects.items():
#            print("Generating doxygen files for {}...".format(prjname))
#            os.makedirs(prjdir, exist_ok=True)
#            cmd = "cd ../_doxygen && doxygen {}.dox".format(prjname)
#            subprocess.call(cmd, shell=True)
#    else:
#        for prjname, prjdir in breathe_projects.items():
#            assert os.path.exists(prjdir) == True, "Regenerate doxygen XML for {}".format(prjname)

breathe_projects = {"verilated": "_build/doxygen/verilated/xml/"}
breathe_default_project = "verilated"
breathe_default_members = ('members')
