// DESCRIPTION: Verilator: Verilog Test module
//
// Test === and !== on interface tristate signals accessed via VarXRef.
// Exercises the getEnExprBasedOnOriginalp() VarXRef path added for #3466.
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

// Simple interface with one external driver
interface ifc;
   logic we;
   tri [7:0] d;
endinterface

module drv (
   ifc io_ifc
);
   assign io_ifc.d = io_ifc.we ? 8'h5A : 8'hzz;
endmodule

// Module that compares interface tri signal via VarXRef (cross-module === / !==)
module chk (
   ifc io_ifc,
   output logic is_z,
   output logic is_5a,
   output logic not_z,
   output logic not_5a
);
   assign is_z = (io_ifc.d === 8'hzz);
   assign is_5a = (io_ifc.d === 8'h5A);
   assign not_z = (io_ifc.d !== 8'hzz);
   assign not_5a = (io_ifc.d !== 8'h5A);
endmodule

// Interface with modport
interface ifc_mp;
   logic we;
   tri [7:0] d;
   modport drv_mp (input we, inout d);
   modport chk_mp (input we, inout d);
endinterface

module drv_mp (
   ifc_mp.drv_mp io_ifc
);
   assign io_ifc.d = io_ifc.we ? 8'h5A : 8'hzz;
endmodule

module chk_mp (
   ifc_mp.chk_mp io_ifc,
   output logic is_z,
   output logic is_5a,
   output logic not_z,
   output logic not_5a
);
   assign is_z = (io_ifc.d === 8'hzz);
   assign is_5a = (io_ifc.d === 8'h5A);
   assign not_z = (io_ifc.d !== 8'hzz);
   assign not_5a = (io_ifc.d !== 8'h5A);
endmodule

// Deep hierarchy: passthru -> drv
module passthru (
   ifc io_ifc
);
   drv u_drv (.*);
endmodule

module t;
   // ---- Basic (no modport) ----
   ifc i ();
   logic is_z, is_5a, not_z, not_5a;
   drv u_drv (.io_ifc(i));
   chk u_chk (.io_ifc(i), .is_z(is_z), .is_5a(is_5a),
              .not_z(not_z), .not_5a(not_5a));

   // ---- Modport ----
   ifc_mp i_mp ();
   logic mp_is_z, mp_is_5a, mp_not_z, mp_not_5a;
   drv_mp u_drv_mp (.io_ifc(i_mp));
   chk_mp u_chk_mp (.io_ifc(i_mp), .is_z(mp_is_z), .is_5a(mp_is_5a),
                     .not_z(mp_not_z), .not_5a(mp_not_5a));

   // ---- Deep hierarchy ----
   ifc i_deep ();
   logic deep_is_z, deep_is_5a, deep_not_z, deep_not_5a;
   passthru u_deep (.io_ifc(i_deep));
   chk u_chk_deep (.io_ifc(i_deep), .is_z(deep_is_z), .is_5a(deep_is_5a),
                    .not_z(deep_not_z), .not_5a(deep_not_5a));

   initial begin
      // Driver off => high-Z
      i.we = 1'b0;
      i_mp.we = 1'b0;
      i_deep.we = 1'b0;
      #1;

      `checkh(is_z, 1'b1);
      `checkh(is_5a, 1'b0);
      `checkh(not_z, 1'b0);
      `checkh(not_5a, 1'b1);
      `checkh(mp_is_z, 1'b1);
      `checkh(mp_is_5a, 1'b0);
      `checkh(mp_not_z, 1'b0);
      `checkh(mp_not_5a, 1'b1);
      `checkh(deep_is_z, 1'b1);
      `checkh(deep_is_5a, 1'b0);

      // Driver on => 8'h5A
      #1;
      i.we = 1'b1;
      i_mp.we = 1'b1;
      i_deep.we = 1'b1;
      #1;

      `checkh(is_z, 1'b0);
      `checkh(is_5a, 1'b1);
      `checkh(not_z, 1'b1);
      `checkh(not_5a, 1'b0);
      `checkh(mp_is_z, 1'b0);
      `checkh(mp_is_5a, 1'b1);
      `checkh(mp_not_z, 1'b1);
      `checkh(mp_not_5a, 1'b0);
      `checkh(deep_is_z, 1'b0);
      `checkh(deep_is_5a, 1'b1);

      // Driver off again => high-Z
      #1;
      i.we = 1'b0;
      i_mp.we = 1'b0;
      i_deep.we = 1'b0;
      #1;

      `checkh(is_z, 1'b1);
      `checkh(is_5a, 1'b0);
      `checkh(not_z, 1'b0);
      `checkh(not_5a, 1'b1);
      `checkh(mp_is_z, 1'b1);
      `checkh(mp_is_5a, 1'b0);
      `checkh(mp_not_z, 1'b0);
      `checkh(mp_not_5a, 1'b1);
      `checkh(deep_is_z, 1'b1);
      `checkh(deep_is_5a, 1'b0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
