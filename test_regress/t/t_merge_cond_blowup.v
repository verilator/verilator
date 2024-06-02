// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   localparam int N = 4096;

   integer cyc = 0;
   reg [63:0] crc= 64'h5aef0c8d_d70a4497;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};

      if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   reg a [N-1:0];
   reg b [N-1:0];

   // This yields pathological complexity for the current conditional merging
   // algorithm. Note in practice, other parts of the compiler blow up on this
   // code far earlier than the conditional merging, but here we go anyway.
   generate
      genvar i;
      for (i = 0 ; i < N ; i = i + 1) begin
        always @(posedge clk) a[i] <= (crc + 64'(i)) == 0 ? crc[(i+16)%64] : crc[(i+32)%64];
      end
      for (i = 0 ; i < N ; i = i + 1) begin
        always @(posedge clk) b[i] <= (crc + 64'(i)) == 0 ? crc[(i+16)%64] : crc[(i+32)%64];
      end
   endgenerate

   always @(posedge clk) begin
      if (cyc >= 2) begin
        for (int i = 0 ; i < N ; i = i + 1) begin
          if (a[i] !== b[i]) begin
            $write("%%Error: %s:%0d: cyc=%0d i=%0d a[i]='h%x b[i]='h%x\n", `__FILE__,`__LINE__, cyc, i, a[i], b[i]);
            $stop;
          end
        end
      end
   end

endmodule
