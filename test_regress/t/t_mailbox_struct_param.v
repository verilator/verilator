// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

package pkg;
  class C #(parameter P = 0);
  typedef struct packed {
    bit [7:0] x;
    } my_t;

    mailbox #(my_t) mb = new();

    task run(output bit [7:0] got);
      my_t v;
      mb.get(v);
      got = v.x;
    endtask
  endclass
endpackage

module top;
  import pkg::*;

  initial begin
    C #(0) c0;
    C #(1) c1;
    C#(0)::my_t s0;
    C#(1)::my_t s1;
    bit [7:0] got0;
    bit [7:0] got1;

    c0 = new();
    c1 = new();

    s0.x = 8'hA5;
    s1.x = 8'h5A;
    c0.mb.put(s0);
    c1.mb.put(s1);

    c0.run(got0);
    c1.run(got1);

    if(got0 !== 8'hA5) $stop;
    if(got0 !== 8'hA5) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
