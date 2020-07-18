// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA

`ifdef USE_VLT
`define HIER_BLOCK
`else
`define HIER_BLOCK /*verilator hier_block*/
`endif

`ifdef AS_PROT_LIB
module secret (
   clk
   );
`else
module t (/*AUTOARG*/
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
   /* verilator lint_off UNOPTFLAT */
   wire [7:0] out3;
   wire [7:0] out3_2;
   /* verilator lint_on UNOPTFLAT */
   wire [7:0] out4;
   wire [7:0] out5;
   int count = 0;

   non_hier_sub0 i_sub0(.clk(clk), .in(out3), .out(out0));
   sub1 i_sub1(.clk(clk), .in(out0), .out(out1));
   sub2 i_sub2(.clk(clk), .in(out1), .out(out2));
   sub3 #(.P0(1)) i_sub3(.clk(clk), .in(out2), .out(out3));
   // Must not use the same wrapper
   sub3 #(.STR("abc"), .P0(1)) i_sub3_2(.clk(clk), .in(out2), .out(out3_2));
   delay #(.N(2), 8) i_delay0(clk, out3, out4);
   delay #(.N(3), 8) i_delay1(clk, out4, out5);

   always_ff @(posedge clk) begin
      if (out3 != out3_2) $stop;
      $display("%d out0:%d %d %d %d %d %d", count, out0, out1, out2, out3, out4, out5);
      if (count == 16) begin
         if (out5 == 15) begin
             $write("*-* All Finished *-*\n");
             $finish;
         end else begin
             $write("Missmatch\n");
             $stop;
         end
      end
      count <= count + 1;
   end
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

   logic [7:0] ff;

   always_ff @(posedge clk) ff <= in;
   assign out = ff;
endmodule

module sub1(
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK

   logic [7:0] ff;

   always_ff @(posedge clk) ff <= in + 1;
   assign out = ff;
endmodule

module sub2(
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK

   logic [7:0] ff;

  // dpi_import_func returns (dpi_eport_func(v) -1)
   import "DPI-C" context function int dpi_import_func(int v);
   export "DPI-C" function dpi_export_func;

   function int dpi_export_func(int v);
       return v + 1;
   endfunction

   always_ff @(posedge clk) ff <= 8'(dpi_import_func({24'b0, in})) + 8'd2;

   non_hier_sub3 i_sub3(.clk(clk), .in(ff), .out(out));

   always @(posedge clk)
      // dotted access within a hierarchical block should be OK
      if (i_sub3.in != ff) begin
         $display("Error mismatch in %m");
         $stop;
      end
endmodule

module non_hier_sub3(
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out);

   wire [7:0] out_2;
   localparam string sparam = "single quote escape comma:'\\,";
   // Parameter appears in the different order from module declaration
   sub3 #(.STR(sparam), .UNUSED(-16'sd3), .P0(8'd3)) i_sub3(.clk(clk), .in(in), .out(out));
   // Instantiate again, should use the same wrapper
   sub3 #(.STR(sparam), .UNUSED(-16'sd3), .P0(8'd3)) i_sub3_2(.clk(clk), .in(in), .out(out_2));
   always @(posedge clk)
      if (out != out_2) $stop;
endmodule

module sub3 #(
   parameter logic [7:0] P0 = 2 + 1,
   type TYPE = logic,
   parameter int UNPACKED_ARRAY[2] = '{0, 1},
   parameter logic signed [15:0] UNUSED = -3,
   parameter string STR = "str") (
   input wire clk,
   input wire [7:0] in,
   output wire [7:0] out); `HIER_BLOCK

   initial $display("P0:%d UNUSED:%d %s", P0, UNUSED, STR);

   TYPE [7:0] ff;
   always_ff @(posedge clk) ff <= in + P0;
   assign out = ff;
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
