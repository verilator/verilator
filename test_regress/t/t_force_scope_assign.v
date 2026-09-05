// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module child (
    input wire drive,
    output wire observed
);
  /*verilator no_inline_module*/

  logic value;

  assign observed = value;

  initial begin
    value = 1'b0;
    if (drive) assign value = 1'b1;
  end
endmodule

module t;
  wire a_observed;
  wire b_observed;
  bit done;

  child a (
      .drive(1'b1),
      .observed(a_observed)
  );
  child b (
      .drive(1'b0),
      .observed(b_observed)
  );

  always @(a_observed or b_observed) begin
    if (!done && a_observed === 1'b1) begin
      done = 1'b1;
      if (b_observed !== 1'b0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
