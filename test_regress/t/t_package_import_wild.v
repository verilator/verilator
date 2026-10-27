// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package pkg_a;
  localparam int ONLY_A = 1;
  localparam int SHARED = 2;
  localparam int SHADOWED = 3;
  function automatic int get_a();
    return 4;
  endfunction
endpackage

package pkg_b;
  localparam int ONLY_B = 10;
  localparam int SHARED = 20;
endpackage

package pkg_c;
  import pkg_a::*;
  export pkg_a::*;
  localparam int ONLY_C = 100;
endpackage

package pkg_d;
  import pkg_b::ONLY_B;  // Imported but not exported, so not visible through pkg_d::*
  localparam int ONLY_D = ONLY_B + 1;
endpackage

package pkg_e;
  import pkg_b::*;
  import pkg_a::*;
  export pkg_a::SHARED;  // Exports pkg_a's, though pkg_b is wildcard imported first
endpackage

interface ifc;
  import pkg_a::*;  // Wildcard imported names are visible through an interface port
  logic sig;
  modport mp(input sig);
endinterface

module sub_ifc (
    ifc i,
    ifc.mp m
);
  initial begin
    `checkd(i.ONLY_A, 1);
    `checkd(i.get_a(), 4);
    `checkd(m.ONLY_A, 1);
  end
endmodule

module sub #(
    parameter int W = 1
);
  import pkg_a::*;
  localparam int SHADOWED = 30;  // Local declaration hides the wildcard import
  initial begin
    `checkd(ONLY_A + W, 1 + W);
    `checkd(SHADOWED, 30);
  end
endmodule

module t;
  import pkg_a::*;
  import pkg_c::*;

  ifc u_ifc ();
  sub_ifc u_sub_ifc (
      .i(u_ifc),
      .m(u_ifc)
  );

  sub #(.W(1)) u_sub1 ();
  sub #(.W(2)) u_sub2 ();

  initial begin
    `checkd(ONLY_A, 1);
    `checkd(ONLY_C, 100);
    `checkd(SHARED, 2);  // Same declaration through pkg_a and pkg_c is not ambiguous
    `checkd(SHADOWED, 3);
    `checkd(get_a(), 4);
    `checkd(pkg_c::SHARED, 2);  // Re-exported from pkg_a
    `checkd(pkg_e::SHARED, 2);
    begin
      // Wildcard import in an unnamed block
      import pkg_d::*;
      import pkg_b::*;
      `checkd(ONLY_B, 10);  // From pkg_b, not the non-exported import in pkg_d
      `checkd(ONLY_D, 11);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
