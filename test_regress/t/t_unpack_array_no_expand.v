// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   output logic [255:0] data_out
   );
   localparam int       NUM_STAGES = 3;

   /* verilator lint_off ALWCOMBORDER */
   /* verilator lint_off UNOPTFLAT */

`define INPUT 256'hbabecafe

   logic [255:0]        stage_data [NUM_STAGES+1];

   genvar               stage;
   generate
      always_comb begin
         stage_data[0] = `INPUT;
      end
      for (stage = 0; stage < NUM_STAGES; ++stage) begin : stage_gen
         always_comb begin
            stage_data[stage+1] = stage_data[stage];
         end
      end
   endgenerate

   /* verilator lint_on UNOPTFLAT */
   /* verilator lint_on ALWCOMBORDER */

   always_comb begin
      data_out = stage_data[NUM_STAGES];
      if (data_out !== `INPUT) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
