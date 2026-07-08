// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
// The '$c(1)' is there to prevent inlining of the signal by V3Gate.
`define IMPURE_ONE ($c(1))
`else
// Use standard $random. The chance of getting 2 consecutive zeroes is negligible.
`define IMPURE_ONE (|($random | $random))
`endif

module t;
  bit [2:0] y;
  bit [2:0] z;
  assign z[0] = 1'b1;
  assign z[1] = !(y[0]);
  assign z[2] = !(|y[1:0]);
  class Foo;
    bit foo;

    task run();
      foo = `IMPURE_ONE;
      if (z !== 3'b001) begin
        $error("Failed: got %0b, expected %0b", z, 3'b001);
      end
      if (foo != 1'b1) $stop;
    endtask
  endclass
  Foo test;
  initial begin
    static Foo foo = new;
    #10 y = 3'b111;
    #1 foo.run();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
