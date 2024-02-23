# DESCRIPTION: Verilator: GDB startup file with useful defines
#
# Copyright 2012-2024 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

define pn
  call AstNode::dumpGdb($arg0)
end
document pn
  Verilator: Print single AstNode NODEP
end

define pnt
  call AstNode::dumpTreeGdb($arg0)
end
document pnt
  Verilator: Print AstNode NODEP's tree
end

# Source python-based gdb config with jshow/jdiff definitions
# (Stored in separate file, so it can be highlighted/linted/formatted as Python)
python
import os
if "VERILATOR_ROOT" in os.environ:
  gdbinit_py = os.environ["VERILATOR_ROOT"] + "/src/.gdbinit.py"
  gdb.execute("source" + gdbinit_py)
end

define jstash
  call (char*) &(AstNode::dumpTreeJsonGdb($arg0)[0])
end
document jstash
Verilator: Perform a JSON dump of the given AST node and save it in value history (e.g. $1) for later
inspection using jtree. The node can be a pointer identifier or an address literal.
end

alias -a js=jstash
alias -a jt=jtree

define dtf
  call AstNode::dumpTreeFileGdb($arg0, 0)
end
document dtf
  Verilator: Dump AstNode tree to file
end

define watchedit
   watch *(AstNode::s_editCntGbl)==$arg0
end
document watchedit
  Verilator: Create watch on where an edit number is made
end
