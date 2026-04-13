// DESCRIPTION: Verilator: Verify function calls through generate-if block references
//
// When a function is defined inside a generate-if block and called via a
// dotted reference (e.g. defs.foo()), the FUNCREF must survive generate
// pruning.  Previously the FUNCREF could point to the deleted else-branch
// function, causing a broken-link internal error.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (  /*AUTOARG*/);
  generate
    if (1) begin : defs
      function automatic logic foo;
        foo = 1'b1;
      endfunction
    end
    else begin : defs
      function automatic logic foo;
        foo = 1'b0;
      endfunction
    end
  endgenerate

  initial begin
    if (defs.foo() !== 1'b1) begin
      $display("%%Error: defs.foo() returned wrong value");
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
