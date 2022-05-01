// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2007 by Peter Debacker.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  reg        [10:0] in;
  reg  signed[7:0]  min;
  reg  signed[7:0]  max;
  wire signed[7:0]  filtered_data;
  reg  signed[7:0]  delay_minmax[31:0];
  integer k;

  initial begin
    in = 11'b10000001000;
    for(k=0;k<32;k=k+1)
      delay_minmax[k] = 0;
  end

   assign filtered_data = $signed(in[10:3]);

   always @(posedge clk) begin
      in = in + 8;
`ifdef TEST_VERBOSE
      $write("filtered_data: %d\n", filtered_data);
`endif
      // delay line shift
      for (k=31;k>0;k=k-1) begin
         delay_minmax[k] = delay_minmax[k-1];
      end
      delay_minmax[0] = filtered_data;
`ifdef TEST_VERBOSE
      $write("delay_minmax[0]  = %d\n", delay_minmax[0]);
      $write("delay_minmax[31] = %d\n", delay_minmax[31]);
`endif
      // find min and max
      min = 127;
      max = -128;
`ifdef TEST_VERBOSE
      $write("max init: %d\n", max);
      $write("min init: %d\n", min);
`endif
      for(k=0;k<32;k=k+1) begin
         if ((delay_minmax[k]) > $signed(max))
           max = delay_minmax[k];
         if ((delay_minmax[k]) < $signed(min))
           min = delay_minmax[k];
      end
`ifdef TEST_VERBOSE
      $write("max: %d\n", max);
      $write("min: %d\n", min);
`endif
      if (min == 127) begin
         $stop;
      end
      else if (filtered_data >= -61) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
