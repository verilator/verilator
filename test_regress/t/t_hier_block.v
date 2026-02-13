// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

`ifdef USE_VLT
`define HIER_BLOCK
`else
`define HIER_BLOCK /*verilator hier_block*/
`endif

`ifdef SHOW_TIMESCALE
`timescale 1ns/1ps
`endif

package stateless_pkg;
  localparam int ONE = 1;
endpackage

`ifdef STATEFUL_PKG
// This is in the $unit package, and will have a copy in every library, which
// is functionally incorrect, but testing it here to make sure it's at least
// traced properly.
logic global_flag = 1'b0;
`endif

interface byte_ifs(input clk);
   logic [7:0] data;
   modport sender(input clk, output data);
   modport receiver(input clk, input data);
endinterface;

typedef enum logic [1:0] {
  enum_val_0 = 2'd0,
  enum_val_1 = 2'd1,
  enum_val_2 = 2'd2,
  enum_val_3 = 2'd3
} enum_t;

typedef enum logic [1:0] {
  alt_enum_0 = 2'd0,
  alt_enum_1 = 2'd1,
  alt_enum_2 = 2'd2,
  alt_enum_3 = 2'd3
} alt_enum_t;

`ifdef AS_PROT_LIB
module secret (
   clk
   );
`else
module t #(
  parameter int PARAM_A = 33,
  parameter int PARAM_B = 44
) (/*AUTOARG*/
   // Inputs
   clk
   );
`endif
   input clk;

`ifdef PROTLIB_TOP
   secret i_secred(.clk(clk));
`else
   wire [7:0] out0;
   wire [7:0] out1;
   wire [7:0] out2;
   wire [7:0] out3;
   wire [7:0] out3_2;
   wire [7:0] out5;
   wire [7:0] out6;
   int count = 0;

   non_hier_sub0 i_sub0(.clk(clk), .in(out3), .out(out0));
   sub1 i_sub1(.clk(clk), .in(out0), .out(out1));
   sub2 i_sub2(.clk(clk), .in(out1), .out(out2));
   sub3 #(.P0(1)) i_sub3(.clk(clk), .in(out2), .out(out3));
   // Must not use the same wrapper
   sub3 #(.STR("abc"), .P0(1)) i_sub3_2(.clk(clk), .in(out2), .out(out3_2));
   delay #(.N(2), 8) i_delay0(clk, out3, out5);
   delay #(.N(3), 8) i_delay1(clk, out5, out6);

   always_ff @(posedge clk) begin
      if (out3 != out3_2) $stop;
`ifndef AS_PROT_LIB
`ifdef PARAM_OVERRIDE
      if (PARAM_A != 100) $stop;
      if (PARAM_B != 200) $stop;
`else
      if (PARAM_A != 33) $stop;
      if (PARAM_B != 44) $stop;
`endif
`endif
      $display("%d %m out0:%d %d %d %d %d", count, out0, out1, out2, out3, out5, out6);
      $display("%d %m child input  ports: %d %d %d", count, i_sub1.in, i_sub2.in, i_sub3.in);
      $display("%d %m child output ports: %d %d %d", count, i_sub1.out, i_sub2.out, i_sub3.out);
      if (count == 16) begin
         if (out6 == 19) begin
             $write("*-* All Finished *-*\n");
             $finish;
         end else begin
             $write("Missmatch\n");
             $stop;
         end
      end
      count <= count + 1;
`ifdef STATEFUL_PKG
      global_flag <= ~global_flag;
`endif
   end

`ifdef CPP_MACRO
   initial begin
      $display("Macro for C++ compiler is defined for Verilator");
      $stop;
   end
`endif

`systemc_implementation
#include <iostream>
#define STRINGIFY_IMPL(str) #str
#define STRINGIFY(str) STRINGIFY_IMPL(str)
namespace {
struct statically_initialized {
   statically_initialized() {
      std::cout << "MACRO:" << STRINGIFY(CPP_MACRO) << " is defined" << std::endl;
   }
} g_statically_initialized;
}
`verilog

`endif  // PROTLIB_TOP

endmodule

module non_hier_sub0(
   input wire clk,
   input wire[7:0] in,
   output wire [7:0] out);

   sub0 i_sub0(.*);

endmodule

module sub0(
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK
`ifdef NO_INLINE
   /* verilator no_inline_module */
`endif

   logic [7:0] ff;

   always_ff @(posedge clk) ff <= in;
   assign out = ff;

`ifdef STATEFUL_PKG
   always_ff @(posedge clk) if (ff[0]) global_flag <= ff[1];
`endif
endmodule

module sub1(
   input wire clk,
   input wire [11:4] in,  // Uses higher LSB to cover bug3539
   output wire [7:0] out); `HIER_BLOCK
`ifdef NO_INLINE
   /* verilator no_inline_module */
`endif

   logic [7:0] ff;
   enum_t enum_v;

   always_ff @(posedge clk) ff <= in + 8'(stateless_pkg::ONE);
   always_ff @(posedge clk) enum_v <= enum_v.next();
   assign out = ff;
endmodule

module sub2(
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK

   logic [7:0] ff;
   alt_enum_t alt_enum_v;

   // dpi_import_func returns (dpi_eport_func(v) -1)
   import "DPI-C" context function int dpi_import_func(int v);
   export "DPI-C" function dpi_export_func;

   function int dpi_export_func(int v);
       return v + 1;
   endfunction

   always_ff @(posedge clk) ff <= 8'(dpi_import_func({24'b0, in})) + 8'd2;
   always_ff @(posedge clk) alt_enum_v <= alt_enum_v.next();

   byte_ifs in_ifs(.clk(clk));
   byte_ifs out_ifs(.clk(clk));
   assign in_ifs.data = ff;
   assign out = out_ifs.data;
   non_hier_sub3 i_sub3(.in(in_ifs), .out(out_ifs));

   always @(posedge clk)
      // dotted access within a hierarchical block should be OK
      if (i_sub3.in_wire != ff) begin
         $display("Error mismatch in %m");
         $stop;
      end
endmodule

module non_hier_sub3(
   byte_ifs.receiver in,
   byte_ifs.sender out);

   wire [7:0] in_wire, out_1, out_2;
   assign in_wire = in.data;
   localparam string sparam = "single quote escape comma:'\\,";
   // Parameter appears in the different order from module declaration
   sub3 #(.STR(sparam), .UNUSED(-16'sd3), .P0(8'd3), .ENUM(enum_val_3)) i_sub3(.clk(in.clk), .in(in.data), .out(out_1));
   // Instantiate again, should use the same wrapper
   sub3 #(.STR(sparam), .UNUSED(-16'sd3), .P0(8'd3), .ENUM(enum_val_3)) i_sub3_2(.clk(in.clk), .in(in.data), .out(out_2));
   always @(posedge in.clk)
      if (out_1 != out_2) $stop;

   assign out.data = out_1;
endmodule

module sub3 #(
   parameter logic [7:0] P0 = 2 + 1,
   type TYPE = logic,
   parameter int UNPACKED_ARRAY[2] = '{0, 1},
   parameter logic signed [15:0] UNUSED = -3,
   parameter string STR = "str",
   parameter enum_t ENUM = enum_val_0) (
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK
`ifdef NO_INLINE
   /* verilator no_inline_module */
`endif

   initial $display("P0:%d UNUSED:%d %s %d", P0, UNUSED, STR, ENUM);

   TYPE [7:0] ff;
   always_ff @(posedge clk) ff <= in + P0;
   always_ff @(posedge clk) if (out4 != out4_2) $stop;

   wire [7:0] out4;
   wire [7:0] out4_2;
   assign out = out4;
   /* verilator lint_off REALCVT */
   sub4 #(.P0(1.6), .P1(3.1), .P3(4.1)) i_sub4_0(.clk(clk), .in(ff), .out(out4));  // incr 2
   sub4 #(.P0(2.4), .P1(3.1), .P3(5)) i_sub4_1(.clk(clk), .in(), .out(out4_2));
   /* verilator lint_on REALCVT */
   /* verilator lint_off ASSIGNIN */
   assign i_sub4_1.in = ff;  // Hierarchical reference to port of hier_block is OK
   /* verilator lint_off ASSIGNIN */

   always @(posedge clk) begin
     $display("%d %m child input  ports: %d %d", $time, i_sub4_0.in, i_sub4_1.in);
     $display("%d %m child output ports: %d %d", $time, i_sub4_0.out, i_sub4_1.out);
   end
endmodule

module sub4 #(
   parameter int P0 = 1.1,
   parameter P1 = 2,
   parameter real P3 = 3) (
   input wire clk,
   input wire [7:0] in,
   output wire[7:0] out); `HIER_BLOCK
`ifdef NO_INLINE
   /* verilator no_inline_module */
`endif

   initial begin
      if (P1 == 2) begin
         $display("P1(%f) is not properly set", P1);
         $stop;
      end
   end

   reg [7:0] ff;
   always_ff @(posedge clk) ff <= in + 8'(P0);
   assign out = ff;

   logic [127:0] sub5_in[2][3];
   wire [7:0] sub5_out[2][3];
   sub5 i_sub5(.clk(clk), .in(sub5_in), .out(sub5_out));

   int count = 0;
   always @(posedge clk) begin
      if (!count[0]) begin
         sub5_in[0][0] <= 128'd0;
         sub5_in[0][1] <= 128'd1;
         sub5_in[0][2] <= 128'd2;
         sub5_in[1][0] <= 128'd3;
         sub5_in[1][1] <= 128'd4;
         sub5_in[1][2] <= 128'd5;
      end else begin
         sub5_in[0][0] <= 128'd0;
         sub5_in[0][1] <= 128'd0;
         sub5_in[0][2] <= 128'd0;
         sub5_in[1][0] <= 128'd0;
         sub5_in[1][1] <= 128'd0;
         sub5_in[1][2] <= 128'd0;
      end
   end

   int driven_from_bind = 0;

   always @(posedge clk) begin
      count <= count + 1;
      if (count > 0) begin
         for (int i = 0; i < 2; ++i) begin
             for (int j = 0; j < 3; ++j) begin
                 automatic byte exp = !count[0] ? 8'(3 * (1 - i) + (2- j) + 1) : 8'b0;
                if (sub5_out[i][j] != exp) begin
                   $display("in[%d][%d] act:%d exp:%d", i, j, sub5_out[i][j], exp);
                   $stop;
                end
                if (i_sub5.out[i][j] != exp) begin
                   $display("in[%d][%d] act:%d exp:%d", i, j, i_sub5.out[i][j], exp);
                   $stop;
                end
            end
         end

         if (driven_from_bind != int'(2*P1)) begin
           $display("%m driven_from_bind: %0d != %0d", driven_from_bind, int'(2*P1));
           $stop;
         end
      end
   end
endmodule

module sub5 (input wire clk, input wire [127:0] in[2][3], output logic [7:0] out[2][3]); `HIER_BLOCK
`ifdef NO_INLINE
   /* verilator no_inline_module */
`endif

   int count = 0;
   always @(posedge clk) begin
      count <= count + 1;
      if (count > 0) begin
         for (int i = 0; i < 2; ++i) begin
            for (int j = 0; j < 3; ++j) begin
               automatic bit [127:0] exp = count[0] ? 128'(3 * i + 128'(j)) : 128'd0;
               if (in[i][j] != exp) begin
                 $display("in[%d][%d] act:%d exp:%d", i, j, in[i][j], exp);
                 $stop;
               end
            end
         end
      end
   end

   always @(posedge clk) begin
      if (count[0]) begin
         out[0][0] <= 8'd6;
         out[0][1] <= 8'd5;
         out[0][2] <= 8'd4;
         out[1][0] <= 8'd3;
         out[1][1] <= 8'd2;
         out[1][2] <= 8'd1;
      end else begin
         out[0][0] <= 8'd0;
         out[0][1] <= 8'd0;
         out[0][2] <= 8'd0;
         out[1][0] <= 8'd0;
         out[1][1] <= 8'd0;
         out[1][2] <= 8'd0;
      end
   end

   wire [7:0] val0[2];
   wire [7:0] val1[2];
   wire [7:0] val2[2];
   wire [7:0] val3[2];
   sub6                   i_sub0(.out(val0));
   sub6 #(.P0(1))         i_sub1(.out(val1));  // Setting the default value
   sub6 #(.P0(1), .P1(2)) i_sub2(.out(val2));  // Setting the default value
   sub6 #(.P0(1), .P1(3)) i_sub3(.out(val3));

   always @(posedge clk) begin
      if (val0[0] != 1 || val0[1] != 2) $stop;
      if (val1[0] != 1 || val1[1] != 2) $stop;
      if (val2[0] != 1 || val2[1] != 2) $stop;
      if (val3[0] != 1 || val3[1] != 3) $stop;
   end
endmodule

module sub6 #(parameter P0 = 1, parameter P1 = 2) (output wire [7:0] out[2]); `HIER_BLOCK
`ifdef NO_INLINE
   /* verilator no_inline_module */
`endif
   assign out[0] = 8'(P0);
   assign out[1] = 8'(P1);
endmodule

module delay #(
   parameter N = 1,
   parameter WIDTH = 8) (
   input wire clk,
   input wire[WIDTH-1:0] in,
   output wire [WIDTH-1:0]out); `HIER_BLOCK

   reg [WIDTH-1:0] tmp;
   always_ff @(posedge clk) tmp <= in;
   if (N > 1) begin
      delay #(.N(N - 1), WIDTH) i_delay(clk, tmp, out);
   end else begin
      assign out = tmp;
   end
endmodule

// Module bound into parametrized hier_block that undergoes name mangling
module sub4_bound #(
  parameter P1 = 1
) (
  output int driven_from_bind
);
  assign driven_from_bind = int'(P1*2);
endmodule

bind sub4 sub4_bound #(.P1(P1)) i_sub4_bound (.*);
