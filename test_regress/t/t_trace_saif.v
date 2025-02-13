// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   state,
   // Inputs
   clk
   );

   input clk;

   int   cyc;
   reg   rstn;
   output [4:0] state;

   integer         fst_integer;
   bit             fst_bit;
   logic           fst_logic;
   int             fst_int;
   shortint        fst_shortint;
   reg [128:0]   fst_longint;
   byte            fst_byte;

   parameter       fst_parameter = 123;
   localparam      fst_lparam = 456;
   supply0         fst_supply0;
   supply1         fst_supply1;
   wire            fst_wire;

   Test test (/*AUTOINST*/
              // Outputs
              .state                    (state[4:0]),
              // Inputs
              .clk                      (clk),
              .rstn                     (rstn));

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;

      fst_longint [ 0 +: 128 ] <= 128'hbeefbeefbeefbeef;

      if (cyc==0) begin
         // Setup
         rstn <= ~'1;
      end
      else if (cyc<10) begin
         rstn <= ~'1;
      end
      else if (cyc<90) begin
         rstn <= ~'0;
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule


module Test (
          input              clk,
          input              rstn,
          output logic [4:0] state
          );

   logic [4:0]               state_w;
   logic [4:0]               state_array [3];
   assign state = state_array[0];

   always_comb begin
      state_w[4] = state_array[2][0];
      state_w[3] = state_array[2][4];
      state_w[2] = state_array[2][3] ^ state_array[2][0];
      state_w[1] = state_array[2][2];
      state_w[0] = state_array[2][1];
   end

   always_ff @(posedge clk or negedge rstn) begin
      if (!rstn) begin
         for (int i = 0; i < 3; i++)
           state_array[i] <= 'b1;
      end
      else begin
         for (int i = 0; i < 2; i++)
           state_array[i] <= state_array[i+1];
         state_array[2] <= state_w;
      end
   end

endmodule
