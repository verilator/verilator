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

interface inf2;
  int k;
endinterface

module GenericModule (interface.mp a);
  initial begin
    a.setup();
  end
endmodule

module t;
  inf inf_inst();
  GenericModule genericModule (inf_inst);
  always begin
    if (inf_inst.v != 3) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
