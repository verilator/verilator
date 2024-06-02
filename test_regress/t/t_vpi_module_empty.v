// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

interface sv_if();
  logic a /*verilator public_flat_rw*/;
endinterface

module top ();

   sv_if sv_if_i();

   // Workaround for bug3937:
   // logic d /*verilator public_flat_rw*/;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
