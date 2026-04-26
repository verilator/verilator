// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc;
  int cntneg;
  logic rst_l;
  wire [1:0] req = cyc[2:1];
  wire gnt = cyc[0];

  // verilator lint_off MULTIDRIVEN
  logic assert_procedural;
  logic assert_immediate;
  wire logic assert_exp = (req == 2'b11) && !gnt && rst_l;
  // verilator lint_off MULTIDRIVEN

  always @(negedge clk) begin
    assert property (disable iff (!rst_l) ((&req) |-> gnt))
    else
      assert_procedural <= 1'b1;
    cntneg <= cntneg + 1;  // To check unlink of above assert
  end

  assert property (@(negedge clk) disable iff (!rst_l) ((&req) |-> gnt))
  else
    assert_immediate <= 1'b1;

  // Test loop
  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d req='b%b gnt=%b  exp=%x proc=%x imm=%x\n", $time, cyc, req, gnt, assert_exp, assert_procedural, assert_immediate);
`endif
    cyc <= cyc + 1;
    assert_procedural <= 0;  // Careful, will race unless assert is on negedge
    assert_immediate <= 0;  // Careful, will race unless assert is on negedge
    if (cyc == 0) begin
      // Setup
      rst_l <= !1'b1;
    end
    else if (cyc < 10) begin
      `checkh(assert_procedural, assert_exp);
      `checkh(assert_immediate, assert_exp);
    end
    else if (cyc == 19) begin
      rst_l <= !1'b0;
    end
    else if (cyc < 30) begin
      `checkh(assert_procedural, assert_exp);
      `checkh(assert_immediate, assert_exp);
    end
    else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
