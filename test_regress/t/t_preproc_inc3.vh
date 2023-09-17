// DESCRIPTION: Verilog::Preproc: Example source code
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2000-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifndef _EXAMPLE_INC2_V_
 `define _EXAMPLE_INC2_V_ 1
 `define _EMPTY
  // FOO
  At file `__FILE__  line `__LINE__
`line `__LINE__ "inc3_a_filename_from_line_directive_with_LINE" 0
  At file `__FILE__  line `__LINE__
`line 100 "inc3_a_filename_from_line_directive" 0
  At file `__FILE__  line `__LINE__

`else
  `error "INC2 File already included once"
`endif // guard

`ifdef not_defined
 `include "NotToBeInced.vh"
`endif
