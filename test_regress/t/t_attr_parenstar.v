// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2011 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  // verilog_format: off
  always @(*) begin
    if (clk) begin end
  end

  always @(* ) begin
    if (clk) begin end
  end

  // Not legal in some simulators, legal in others
//  always @(* /*cmt*/ ) begin
//    if (clk) begin end
//  end

  // Not legal in some simulators, legal in others
//  always @(* // cmt
//       ) begin
//    if (clk) begin end
//  end

  always @ (*
         ) begin
    if (clk) begin end
  end
  // verilog_format: on

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
