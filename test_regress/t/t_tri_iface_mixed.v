// DESCRIPTION: Verilator: Verilog Test module
//
// Test mixed local + external tristate drivers on the same interface signal.
// The interface contains a local driver, and an external module also drives
// the same tri signal through a port.
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

// Basic interface with local driver (no modport)
interface ifc;
   logic we_local;
   logic we_ext;
   tri [7:0] d;
   // Local driver inside the interface
   assign d = we_local ? 8'hA5 : 8'hzz;
endinterface

module drv (
   ifc io_ifc
);
   // External driver from a different module
   assign io_ifc.d = io_ifc.we_ext ? 8'h3C : 8'hzz;
endmodule

// Interface with modport and local driver
interface ifc_mp;
   logic we_local;
   logic we_ext;
   tri [7:0] d;
   modport drv_mp (input we_ext, inout d);
   // Local driver inside the interface
   assign d = we_local ? 8'hA5 : 8'hzz;
endinterface

module drv_mp (
   ifc_mp.drv_mp io_ifc
);
   // External driver through modport
   assign io_ifc.d = io_ifc.we_ext ? 8'h3C : 8'hzz;
endmodule

module t;
   ifc i ();
   drv u (.io_ifc(i));

   ifc_mp i_mp ();
   drv_mp u_mp (.io_ifc(i_mp));

   initial begin
      i.we_local = 1'b0;
      i.we_ext = 1'b0;
      i_mp.we_local = 1'b0;
      i_mp.we_ext = 1'b0;
      #1;

      // ---- Basic (no modport) ----

      // Both drivers off => high-Z
      `checkh(i.d, 8'hzz);

      // Local driver only
      #1;
      i.we_local = 1'b1;
      i.we_ext = 1'b0;
      #1;
      `checkh(i.d, 8'hA5);

      // External driver only
      #1;
      i.we_local = 1'b0;
      i.we_ext = 1'b1;
      #1;
      `checkh(i.d, 8'h3C);

      // Both drivers on (OR of 8'hA5 and 8'h3C in Verilator's tristate model)
      #1;
      i.we_local = 1'b1;
      i.we_ext = 1'b1;
      #1;
      `checkh(i.d, 8'hBD);

      // Both drivers off again
      #1;
      i.we_local = 1'b0;
      i.we_ext = 1'b0;
      #1;
      `checkh(i.d, 8'hzz);

      // ---- Modport-based external access ----

      // Both drivers off => high-Z
      `checkh(i_mp.d, 8'hzz);

      // Local driver only
      #1;
      i_mp.we_local = 1'b1;
      i_mp.we_ext = 1'b0;
      #1;
      `checkh(i_mp.d, 8'hA5);

      // External driver only (through modport)
      #1;
      i_mp.we_local = 1'b0;
      i_mp.we_ext = 1'b1;
      #1;
      `checkh(i_mp.d, 8'h3C);

      // Both drivers on (OR of 8'hA5 and 8'h3C in Verilator's tristate model)
      #1;
      i_mp.we_local = 1'b1;
      i_mp.we_ext = 1'b1;
      #1;
      `checkh(i_mp.d, 8'hBD);

      // Both drivers off again
      #1;
      i_mp.we_local = 1'b0;
      i_mp.we_ext = 1'b0;
      #1;
      `checkh(i_mp.d, 8'hzz);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
