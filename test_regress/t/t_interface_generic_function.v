// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
  function int get();
    return v;
  endfunction
endinterface

interface inf2;
  int k;
endinterface

module GenericModule (interface a);
  initial begin
    if (a.get() != 4) $stop;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst.v = 4;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
