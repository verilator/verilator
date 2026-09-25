// DESCRIPTION: Verilator: Test masking of shifted values with dirty upper bits (#8500)
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  logic clk = 1'b0;
  always #5 clk = ~clk;

  int cyc = 0;
  logic [31:0] src;
  logic [64:0] out;

  sub sub (.*);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      src <= 32'hffffffff;
    end
    else if (cyc == 2) begin
      `checkh(out, 65'h1_000000ff_fffeff00);
      src <= 32'h12345678;
    end
    else if (cyc == 4) begin
      `checkh(out, 65'h0_00000012_3456_7800);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module sub (
    input logic clk,
    input logic [31:0] src,
    output logic [64:0] out
);
  logic [64:0] q  /*verilator public_flat_rw*/;
  always_ff @(posedge clk) begin
    q <= '0;
    q[15:8] <= src[7:0];
    q[39:16] <= {src[31:9], 1'b0};
    q[64] <= src[8];
  end
  assign out = q;
endmodule
