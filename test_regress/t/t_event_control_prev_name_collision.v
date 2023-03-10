// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0
module S(
  input  reset,
         io_i,
  output io_o
);
  reg s;
  always @(posedge reset) begin
    if (reset) begin
      s <= 1'h0;
    end
    else begin
      s <= io_i;
    end
  end
  assign io_o = s;
endmodule

module Q(
  input        reset_e,
  input        reset_d,
  output       ready_e
);

  wire       reset_n;
  wire       io_v;
  wire       io_e;
  S e (
    .io_i  (),
    .reset  (reset_e | ~reset_n),
    .io_o (io_e)
  );
  S v (
    .io_i  (io_e),
    .reset  (reset_e),
    .io_o (io_v)
  );
  assign reset_n = ~reset_d;
  assign ready_e = io_v;
endmodule

module Test(
  input        	reset,
  output        valid
);
  wire ready_e;

  Q q (
    .reset_e (reset),
    .reset_d (reset),
    .ready_e (ready_e)
  );

  assign valid = ready_e;
endmodule

module Test2(
  input         reset,
  input         valid
);
  always begin
    if (~reset & valid) begin
        $fatal;
    end
  end
endmodule

module Dut(
  input  reset
);
  wire        valid_g;

  Test t (
    .reset       (reset),
    .valid       (valid_g)
  );
  Test2 t2 (
    .reset       (reset),
    .valid       (valid_g)
  );
endmodule

module t (/*AUTOARG*/
   );
  reg  [$bits(dut.reset)-1:0] reset;

  Dut dut (
      .reset(reset)
  );
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
