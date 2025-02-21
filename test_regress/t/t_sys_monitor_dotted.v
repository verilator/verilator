// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface addsub_ifc;
   logic [7:0] a, b;
   logic doAdd0;
   logic clk;
   logic rst_n;
   logic [7:0] result;
   logic overflow;
endinterface

module adder_sub_8bit
  (
   input logic clk,
   input logic rst_n,
   input logic [7:0] a,
   input logic [7:0] b,
   input logic doAdd0,
   output logic [7:0] result,
   output logic overflow
   );

   logic [7:0] b_modified;
   logic [8:0] temp_result;

   assign b_modified = doAdd0 ? b : ~b + 8'b1;

   always_comb begin
      temp_result = {1'b0, a} + {1'b0, b_modified};
   end

   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
         result <= 8'h0;
         overflow <= 1'b0;
      end else begin
         result <= temp_result[7:0];
         overflow <= (a[7] == b_modified[7] && result[7] != a[7]);
      end
   end

endmodule

module t;
   addsub_ifc dut_ifc();

   adder_sub_8bit dut
     (
      .clk(dut_ifc.clk),
      .rst_n(dut_ifc.rst_n),
      .a(dut_ifc.a),
      .b(dut_ifc.b),
      .doAdd0(dut_ifc.doAdd0),
      .result(dut_ifc.result),
      .overflow(dut_ifc.overflow)
      );

   initial begin
      dut_ifc.clk = 0;
      forever #5 dut_ifc.clk = ~dut_ifc.clk;
   end

   initial begin
      dut_ifc.rst_n = 0;
      dut_ifc.a = 8'h0;
      dut_ifc.b = 8'h0;
      dut_ifc.doAdd0 = 1'b1;

      #10 dut_ifc.rst_n = 1;

      #10;
      dut_ifc.a = 8'h35;
      dut_ifc.b = 8'h42;
      dut_ifc.doAdd0 = 1'b1;

      #20;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   initial begin
      $display("[%0t] Initial rst_n=%b a=%h b=%h doAdd0=%b result=%h overflow=%b",
               $time, dut_ifc.rst_n, dut_ifc.a, dut_ifc.b,
               dut_ifc.doAdd0, dut_ifc.result, dut_ifc.overflow);
      $monitor("[%0t] Monitor rst_n=%b a=%h b=%h doAdd0=%b result=%h overflow=%b",
               $time, dut_ifc.rst_n, dut_ifc.a, dut_ifc.b,
               dut_ifc.doAdd0, dut_ifc.result, dut_ifc.overflow);
   end

endmodule
