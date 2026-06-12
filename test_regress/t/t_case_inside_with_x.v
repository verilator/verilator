// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module top;
  bit clk = 1'b0;
  always #1 clk = ~clk;

  logic [2:0] cyc = 3'd0;
  int count = 0;
  always @(posedge clk) begin
    // verilator lint_off CASEWITHX
    case (cyc) inside
      3'b000: begin $display("case inside 000"); ++count; end
      3'b001: begin $display("case inside 001"); ++count; end
      // Should match z
      3'b01?: begin $display("case inside 01?"); ++count; end
      // Should match x
      3'b1xx: begin $display("case inside 1xx"); ++count; end
    endcase
    // verilator lint_on CASEWITHX
    cyc <= cyc + 3'd1;
    if (&cyc) begin
      `checkh(count, 8);
      $finish;
    end
  end
endmodule
