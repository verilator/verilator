// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface inf;
  int v;
  task setup();
    v = 3;
  endtask
  modport mp(
    input v
  );
endinterface

module GenericModule (interface.mp a);
  initial begin
    #1;
    if (a.v != 3) $stop;
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  initial begin
    inf_inst.setup();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
