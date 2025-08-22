// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
endinterface

interface inf2;
  int k;
endinterface

module GenericModule (logic[31:0] l1, interface a, logic[31:0] l2, interface b);
  initial begin
    #1;
    if (l1 != 87) $stop;
    if (a.v != 7) $stop;
    if (l2 != 73) $stop;
    if (b.k != 9) $stop;
  end
endmodule

module t;
  inf inf_inst();
  inf2 inf_inst2();
  GenericModule genericModule (87, inf_inst, 73, inf_inst2);
  initial begin
    inf_inst.v = 7;
    inf_inst2.k = 9;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
