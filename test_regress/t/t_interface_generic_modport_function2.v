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
  modport mp(
    output v
  );
endinterface

interface inf2;
  int k;
endinterface

module GenericModule (interface.mp a);
  initial begin
    a.v = 5;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  always begin
    if(inf_inst.get() != 5) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
