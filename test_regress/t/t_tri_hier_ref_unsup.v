// DESCRIPTION: Verilator: Verilog Test module
//
// Test case #1: Hierarchical write to a non-interface submodule's tri wire.
// A parent module drives a child module's internal tri wire via hierarchical
// reference, in addition to the child's own internal driver.
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

// verilator lint_off MULTIDRIVEN

module sub_with_tri (
   input we_internal
);
   tri [7:0] bus;
   // Internal driver: drives 8'hAA when we_internal is high
   assign bus = we_internal ? 8'hAA : 8'hzz;
endmodule

module t;
   logic sub_we_internal;
   sub_with_tri u_sub(.we_internal(sub_we_internal));

   logic hier_we;
   // Drive u_sub.bus hierarchically from this module
   assign u_sub.bus = hier_we ? 8'hBB : 8'hzz;

   initial begin
      // All drivers off -> high-Z
      #1;
      hier_we = 1'b0;
      sub_we_internal = 1'b0;
      #1;
      `checkh(u_sub.bus, 8'hzz);

      // External hierarchical driver on
      #1;
      hier_we = 1'b1;
      sub_we_internal = 1'b0;
      #1;
      `checkh(u_sub.bus, 8'hBB);

      // Internal driver on, external off
      #1;
      hier_we = 1'b0;
      sub_we_internal = 1'b1;
      #1;
      `checkh(u_sub.bus, 8'hAA);

      // Both off again
      #1;
      hier_we = 1'b0;
      sub_we_internal = 1'b0;
      #1;
      `checkh(u_sub.bus, 8'hzz);

      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
