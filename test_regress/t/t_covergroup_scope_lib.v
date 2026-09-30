// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Modules of one name in distinct libraries are distinct, as are the covergroup types declared
// in them (IEEE 1800-2023 19.3, 33).  m3 of liba is covered and m3 of libb is not; were their
// covergroups one type, both would be 50.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  m1 u_1 ();  // Instantiates m3 of liba
  m2 u_2 ();  // Instantiates m3 of libb

  initial begin
    u_1.u_13.inst.sample(0);
    u_1.u_13.inst.sample(1);
    `checkr(u_1.u_13.inst.get_coverage(), 100.0);
    `checkr(u_2.u_23.inst.get_coverage(), 0.0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
