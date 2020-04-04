# DESCRIPTION: Verilator: GDB startup file with useful defines
#
# Copyright 2012-2020 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

define pn
  call $arg0->dumpGdb()
end
document pn
  Verilator: Print single AstNode NODEP
end

define pnt
  call $arg0->dumpTreeGdb()
end
document pnt
  Verilator: Print AstNode NODEP's tree
end

define dtf
  call AstNode::dumpTreeFileGdb(0)
end
document dtf
  Verilator: Dump AstNode tree to file
end

define watchedit
   watch AstNode::s_editCntGbl==$arg0
end
document watchedit
  Verilator: Create watch on where a edit number is made
end
