// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   data_o,
   // Inputs
   clk, rst_i, write_valid_i, write_front_i, read_valid_i, data_i
   );

   localparam NR_ELEMENTS = 16;
   localparam DATAW = 32;

   input clk;
   input rst_i;
   input write_valid_i;
   input write_front_i;
   input read_valid_i;
   input [31:0] data_i;
   output [31:0] data_o;

   reg [31:0] FIFOContent [NR_ELEMENTS-1:0];

   typedef logic [$clog2(NR_ELEMENTS)-1:0] FIFOPointer_t;

   // verilator lint_off WIDTH
   localparam FIFOPointer_t MAX_PTR_VAL = NR_ELEMENTS-1;
   // verilator lint_on WIDTH
   localparam FIFOPointer_t MIN_PTR_VAL = 0;
   localparam FIFOPointer_t PTR_INC = 1;
   FIFOPointer_t write_pointer;
   FIFOPointer_t read_pointer;

   function FIFOPointer_t nextPointer(input FIFOPointer_t val);
      if ($clog2(NR_ELEMENTS) == $clog2(NR_ELEMENTS+1)
          && val == MAX_PTR_VAL)
        nextPointer = MIN_PTR_VAL; // explicit wrap if NR_ELEMENTS is not a power of 2
      else
        nextPointer = val + PTR_INC;
   endfunction

   function FIFOPointer_t prevPointer(input FIFOPointer_t val);
      if ($clog2(NR_ELEMENTS) == $clog2(NR_ELEMENTS+1)
          && val == MIN_PTR_VAL)
        prevPointer = MAX_PTR_VAL; // explicit wrap if NR_ELEMENTS is not a power of 2
      else
        prevPointer = val - PTR_INC;
   endfunction

   reg [$clog2(NR_ELEMENTS)-1:0] level;
   reg is_empty;

   always @(posedge clk) begin
      if (write_valid_i)
        FIFOContent[write_front_i ? (read_valid_i ? read_pointer : prevPointer(read_pointer)) : write_pointer] <= data_i;
   end

   assign data_o = FIFOContent[read_pointer];

   always @(posedge clk) begin
      if (rst_i) begin
         is_empty <= 1;
      end
      else if (write_valid_i) begin
         is_empty <= 0;
      end
      else if (read_valid_i && write_pointer == nextPointer(read_pointer)) begin
         is_empty <= 1;
      end
   end

   always @(posedge clk) begin
      if (rst_i) begin
         level <= 0;
      end
      else begin
         level <= level + (write_valid_i ? 1 : 0) - (read_valid_i ? 1 : 0);
      end
   end

   always @(posedge clk) begin
      if (rst_i) begin
         write_pointer <= 0;
      end
      else if (write_valid_i && !write_front_i) begin
         write_pointer <= nextPointer(write_pointer);
      end
   end

   always @(posedge clk) begin
      if (rst_i) begin
         read_pointer <= 0;
      end
      else if (read_valid_i) begin
         if (!(write_valid_i && write_front_i))read_pointer <= nextPointer(read_pointer);
      end
      else if (write_valid_i && write_front_i) begin
         read_pointer <= prevPointer(read_pointer);
      end
   end
endmodule
