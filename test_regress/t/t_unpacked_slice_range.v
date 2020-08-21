// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA

module t (
   clk
   );
   input clk;

   // unpack_sig0[6] and unpack_sig1[6] are expected to have the
   // same value regard less of their extent
   logic unpack_sig0 [0:6];
   logic unpack_sig1 [3:6];

   always @(posedge clk) begin
      unpack_sig0[3] <= 1'b1;
      unpack_sig1[3] <= 1'b1;
      unpack_sig0 [4:6] <= unpack_sig0[3:5];
      unpack_sig1 [4:6] <= unpack_sig1[3:5];
   end

   int c = 0;
   always @(posedge clk) begin
      c <= c + 1;
      if (c == 4) begin
         if (!unpack_sig0[6] || !unpack_sig1[6]) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end else begin
         if (unpack_sig0[6] || unpack_sig1[6]) $stop;
      end
   end
endmodule
