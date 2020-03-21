// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Roman Popov.
// SPDX-License-Identifier: CC0-1.0

module dut
  #(
    parameter DEPTH = 16,
    parameter WIDTH = 32,
    parameter RAM_SPLIT_WIDTH = 16
    )
   (
    output logic [WIDTH-1:0] ram_dataout
    );

   localparam RAM_ADDR_WIDTH = $clog2(DEPTH);  // = 4
   localparam NUM_RAM_BLOCKS = (WIDTH/RAM_SPLIT_WIDTH) + {31'h0, ((WIDTH % RAM_SPLIT_WIDTH) > 0)};  // = 2
   typedef logic [NUM_RAM_BLOCKS:0][31:0] block_index_t;  // width 96

   function automatic block_index_t index_calc(input int WIDTH, NUM_RAM_BLOCKS);
      index_calc[0] = '0;
      for(int i = 0; i < NUM_RAM_BLOCKS; i++) index_calc[i+1] = WIDTH/NUM_RAM_BLOCKS + {31'h0, (i < (WIDTH%NUM_RAM_BLOCKS))};
      for(int i = 0; i < NUM_RAM_BLOCKS; i++) index_calc[i+1] = index_calc[i+1] + index_calc[i];
      // bug1467 was this return
      return index_calc;
   endfunction

   localparam block_index_t RAM_BLOCK_INDEX = index_calc(WIDTH, NUM_RAM_BLOCKS);

   generate
      begin : ram_dataout_gen
         for (genvar i = 0; i < NUM_RAM_BLOCKS; i++) begin
            always_comb ram_dataout[RAM_BLOCK_INDEX[i+1]-1:RAM_BLOCK_INDEX[i]] = 0;
         end
      end
   endgenerate

   initial begin
      if (RAM_BLOCK_INDEX != {32'd32, 32'd16, 32'd0}) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module t
  (
   input               clk,
   output logic [31:0] ram_dataout
   );

   dut dut0(.*);

endmodule
