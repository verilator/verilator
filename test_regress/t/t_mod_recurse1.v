// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Sean Moore.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   rec rec ();

endmodule

module rec;
   parameter DEPTH = 1;

   generate
      if (DEPTH==1) begin
         rec #(.DEPTH(DEPTH+1)) sub;
      end
      else if (DEPTH==2) begin
         rec #(.DEPTH(DEPTH+1)) subb;
      end
      else if (DEPTH==3) begin
         bottom #(.DEPTH(DEPTH+1)) bot;
      end
   endgenerate
endmodule

module bottom;
   parameter DEPTH = 1;
   initial begin
      if (DEPTH!=4) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
