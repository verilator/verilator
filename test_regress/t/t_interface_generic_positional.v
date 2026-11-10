// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface ifc;
  int v;
endinterface

interface inf2;
  int k;
endinterface

module GenericModule (
    interface a,
    interface b
);
  initial begin
    #1;
    `checkd(a.v, 7);
  end
endmodule

module GenericModule2 (
    interface a,
    input int marker,
    interface b
);
  initial begin
    #1;
    `checkd(a.v, 7);
    `checkd(marker, 9);
    b.k = 9;
  end
endmodule

module t;
  ifc inf_inst[3] ();
  GenericModule genericModule (
      .a(inf_inst[1]),
      .b(inf_inst[2])
  );
  // Named connections in other than the port order
  inf2 inf_inst2 ();
  GenericModule2 genericModule2 (
      .b(inf_inst2),
      .marker(9),
      .a(inf_inst[1])
  );
  initial begin
    inf_inst[1].v = 7;
    #2;
    `checkd(inf_inst2.k, 9);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
