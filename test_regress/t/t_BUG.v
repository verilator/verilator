// DESCRIPTION: Verilator: Verilog Test module
//
// Minimal reproducer for Verilator 5.048 internal error:
//   V3Force.cpp:216: `force` assignment has no VarRef on LHS
//
// This reproducer requires `--trace` to trigger the bug.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc;
  logic done;
  logic forced_sig;

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  logic out;  // From test of Test.v
  // End of automatics

  Test test (  /*AUTOINST*/
             // Outputs
             .out                       (out),
             // Inputs
             .clk                       (clk));

  initial begin
    force forced_sig = 1'b1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      done <= 1'b0;
    end else if (cyc == 2) begin
      done <= out;
    end else if (cyc == 3) begin
      `checkh(done, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    input clk,
    output logic out
);

  typedef struct {
    logic [7:0] d[0:3];
  } payload_t;

  payload_t s;
  logic [7:0] arr[0:3];

  always_comb begin
    s.d = arr;
  end

  always @(posedge clk) begin
    out <= 1'b1;
  end
endmodule
