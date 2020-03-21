// DESCRIPTION: Verilator: Check initialisation of cloned clock variables
//
// This tests issue 1327 (Strange initialisation behaviour with
// "VinpClk" cloned clock variables)
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Rupert Swarbrick (Argon Design).
// SPDX-License-Identifier: CC0-1.0

// bug1327
// This models some device under test with an asynchronous reset pin
// which counts to 15.
module dut (input wire  clk,
            input wire  rst_n,
            output wire done);

   reg [3:0] counter;

   always @(posedge clk or negedge rst_n) begin
      if (rst_n & ! clk) begin
         $display("[%0t] %%Error: Oh dear! 'always @(posedge clk or negedge rst_n)' block triggered with clk=%0d, rst_n=%0d.",
                  $time, clk, rst_n);
         $stop;
      end

      if (! rst_n) begin
         counter <= 4'd0;
      end else begin
         counter <= counter < 4'd15 ? counter + 4'd1 : counter;
      end
   end

   assign done = rst_n & (counter == 4'd15);
endmodule


module t(input wire clk,
         input wire rst_n);

   wire dut_done;

   // A small FSM for driving the test
   //
   // This is just designed to be enough to force Verilator to make a
   // "VinpClk" variant of dut_rst_n.

   // Possible states:
   //
   //   0: Device in reset
   //   1: Device running
   //   2: Device finished
   reg [1:0] state;
   always @(posedge clk or negedge rst_n) begin
      if (! rst_n) begin
         state <= 0;
      end else begin
         if (state == 2'd0) begin
            // One clock after resetting the device, we switch to running
            // it.
            state <= 2'd1;
         end
         else if (state == 2'd1) begin
            // If the device is running, we switch to finished when its
            // done signal goes high.
            state <= dut_done ? 2'd2 : 2'd1;
         end
         else begin
            // If the dut has finished, the test is done.
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

   wire dut_rst_n = rst_n & (state != 0);

   wire done;
   dut dut_i (.clk   (clk),
              .rst_n (dut_rst_n),
              .done  (dut_done));

endmodule
