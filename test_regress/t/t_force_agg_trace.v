// DESCRIPTION: Verilator: Verilog Test module
//
// Trace instrumentation over forces on unpacked aggregates.  Two cases that
// only failed under --trace:
//  - A self-assigning whole-struct force, which is removed as redundant before
//    V3Force, left a release behind whose trace read asserted internally.
//  - Forcing the same unpacked-array member in two elements of an interface
//    instance array added a same-named read helper to the shared interface
//    class twice, which trace kept live and the C++ compiler then rejected.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

interface Bus;
  logic [7:0] data[2];
endinterface

// verilog_format: off
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)
// verilog_format: on

module t;
  typedef struct {
    logic [7:0] x;
    logic [7:0] y;
  } pair_t;
  pair_t s;

  Bus buses[2] ();

  initial begin
    s.x = 8'h12;
    s.y = 8'h34;
    // Removed as redundant before V3Force; its release must not fault under trace
    force s = s;
    #1;
    `checkh(s.x, 8'h12);
    `checkh(s.y, 8'h34);
    release s;

    for (int i = 0; i < 2; ++i) begin
      buses[0].data[i] = 8'h10 + 8'(i);
      buses[1].data[i] = 8'h20 + 8'(i);
    end
    #1;
    force buses[0].data[1] = 8'ha0;
    force buses[1].data[1] = 8'hb1;
    #1;
    `checkh(buses[0].data[1], 8'ha0);
    `checkh(buses[1].data[1], 8'hb1);
    `checkh(buses[0].data[0], 8'h10);
    `checkh(buses[1].data[0], 8'h20);
    release buses[0].data[1];
    release buses[1].data[1];
    #1;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
