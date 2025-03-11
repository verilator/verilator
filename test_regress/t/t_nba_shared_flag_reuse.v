// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

module t;

  reg clk = 1'b1;
  reg reset = 1'b1;

  reg aw_valid = 1'b0;
  reg w_valid = 1'b0;

  reg r_valid;

  reg [31:0] addr [1:0];
  reg [7:0] len [1:0];

  always #5 clk = ~clk;

  initial begin
    #5; // Align with negedge clk

    #20;
    `checkh(addr[0], 32'h0000_0000);
    reset = 1'b0;

    #20;
    `checkh(addr[0], 32'h0000_0000);
    aw_valid = 1'b1;
    w_valid = 1'b1;

    #10;
    `checkh(addr[0], 32'h4444_4444);
    aw_valid = 1'b0;

    #10;
    `checkh(addr[0], 32'h2222_2222);
    w_valid = 1'b0;

    #10;
    `checkh(addr[0], 32'h2222_2222);
    $write("*-* All Finished *-*\n");
    $finish;
  end


  always @(posedge clk) begin
    if (reset) begin
      r_valid <= 0;
    end
    else begin
      if (r_valid) begin
        addr[0] <= 32'h11111111;
        len[0] <= len[0] - 1;
      end
      if (w_valid) begin
        addr[0] <= 32'h22222222;
      end
      if (aw_valid) begin
        addr[0] <= 32'h33333333;
        len[0] <= 8'hff;
        if (w_valid)
          addr[0] <= 32'h44444444;
      end
    end
  end
endmodule
