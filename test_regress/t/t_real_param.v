// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module foo
  #( parameter real BAR = 2.0)
   ();
endmodule

module t();
   genvar m, r;
   generate
      for (m = 10; m <= 20; m+=10) begin : gen_m
         for (r = 0; r <= 1; r++) begin : gen_r
            localparam real LPARAM = m + (r + 0.5);
            initial begin
                if (LPARAM != foo_inst.BAR) begin
                   $display("%m: LPARAM != foo_inst.BAR (%f, %f)",
                            LPARAM, foo_inst.BAR);
                   $stop();
                end
            end

            foo #(.BAR (LPARAM)) foo_inst ();
         end
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
