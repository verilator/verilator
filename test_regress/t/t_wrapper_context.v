// DESCRIPTION: Verilator: Verilog Test module
//
// This model counts from 0 to 10. It is instantiated twice in concurrent
// threads to check for race conditions/signal interference.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020-2021 by Andreas Kuster.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module top
  (
   input             clk,
   input             rst,
   input [31:0]      trace_number,
   input             stop,
   output bit [31:0] counter,
   output bit        done_o
   );

   initial begin
      string number;
      string filename;
      number.itoa(trace_number);
      filename = {`STRINGIFY(`TEST_OBJ_DIR), "/trace", number, ".vcd"};
      $display("Writing dumpfile '%s'", filename);
      $dumpfile(filename);
      $dumpvars();
   end

   always@(posedge clk) begin
      if (rst)
        counter <= 0;
      else
        counter <= counter + 1;
   end
   always_comb begin
      done_o = '0;
      if (stop) begin
         if (counter >= 5 && stop) begin
            done_o = '1;
            $stop;
         end
      end
      else begin
         if (counter >= 10) begin
            done_o = '1;
            $finish;
         end
      end
   end

endmodule
