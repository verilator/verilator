// DESCRIPTION: Verilator: Verilog Test module
//
// Test case #4: $root absolute hierarchical reference to tristate signal.
// A submodule reads a tristate signal from the top module via $root.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub_root_reader (
   output logic [7:0] val
);
   assign val = $root.t.root_bus;
endmodule

module t;
   tri [7:0] root_bus;
   logic root_we;
   assign root_bus = root_we ? 8'hCC : 8'hzz;

   logic [7:0] root_readback;
   sub_root_reader u_reader(.val(root_readback));

   initial begin
      #1;
      root_we = 1'b0;
      #1;
      `checkh(root_readback, 8'hzz);

      #1;
      root_we = 1'b1;
      #1;
      `checkh(root_readback, 8'hCC);

      #1;
      root_we = 1'b0;
      #1;
      `checkh(root_readback, 8'hzz);

      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
