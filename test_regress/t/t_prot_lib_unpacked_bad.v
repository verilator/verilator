// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module secret_impl (
                    input  unpacked_in [7:0],
                    output unpacked_out [7:0]);

   genvar                  i;
   generate
      for (i = 0; i < 8; i = i + 1) begin
         assign unpacked_out[i] = unpacked_in[i];
      end
   endgenerate

endmodule
