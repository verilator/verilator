// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

module t(/*AUTOARG*/
   // Inputs
   clk
   );

  input clk;

  logic [31:0] cnt = 0;

  logic [31:0] out0;
  logic [31:0] out1;
  logic [31:0] out2;
  logic [31:0] out3;

  // Splittable
  sub #(.ADDEND(1), .FORCEABLE(1'b0)) sub_0(clk, cnt, out0);
  // Unsplittable due to hierarchical reference
  sub #(.ADDEND(2), .FORCEABLE(1'b0)) sub_1(clk, cnt, out1);
  // Unsplittable due to hiererchical reference
  sub #(.ADDEND(3), .FORCEABLE(1'b0)) sub_2(clk, cnt, out2);
  // Unsplittable due to forceable attribute
  sub #(.ADDEND(4), .FORCEABLE(1'b1)) sub_3(clk, cnt, out3);

  task print();
    // This hierarchical reference should prevent automatic splitting
    $display("sub_2.gen_else.tmp[9]: %02d", sub_2.gen_else.tmp[9]);
  endtask

  always @(posedge clk) begin
    `checkh(out0, cnt + 32'd10);
    `checkh(out1, cnt + 32'd20);
    `checkh(out2, cnt + 32'd30);
    `checkh(out3, cnt + 32'd40);

     // This hierarchical reference should prevent automatic splitting
     $display("sub_1.gen_else.tmp[9]: %02d", sub_1.gen_else.tmp[9]);
     print();

     cnt <= cnt + 32'd1;

     if (cnt == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
     end
  end

endmodule

module sub #(
  parameter logic [31:0] ADDEND,
  parameter logic FORCEABLE
) (
  input wire clk,
  input logic [31:0] i,
  output logic [31:0] o
);
  /* verilator lint_off UNOPTFLAT */
  // Both branches do the same thing, difference is the 'forceable' attribute
  if (FORCEABLE) begin : gen_then
    wire logic [9:0][31:0] tmp /* verilator forceable */;
    assign tmp[0] = i;
    for (genvar n = 1; n < 10; ++n) begin
      assign tmp[n] = tmp[n-1] + ADDEND;
    end
    assign o = tmp[9] + ADDEND;
  end else begin : gen_else
    wire logic [9:0][31:0] tmp;
    assign tmp[0] = i;
    for (genvar n = 1; n < 10; ++n) begin
      assign tmp[n] = tmp[n-1] + ADDEND;
    end
    assign o = tmp[9] + ADDEND;
  end

  /* verilator lint_on UNOPTFLAT */
endmodule
