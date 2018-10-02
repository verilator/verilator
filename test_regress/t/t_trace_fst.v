// This file ONLY is placed into the Public Domain, for any use,
// Author: Yu-Sheng Lin johnjohnlys@media.ee.ntu.edu.tw

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

   Test test (/*AUTOINST*/
              // Outputs
              .state                    (state[4:0]),
              // Inputs
              .clk                      (clk),
              .rstn                     (rstn));

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
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
