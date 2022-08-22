// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   integer cyc = 0;

   reg [7:0] a;
   reg [127:0] b;

   always #1 begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         a <= 8'hFF;
         a[7] <= 1'b0;
      end
      else if (cyc == 1) begin
`ifdef TEST_VERBOSE
         $write("a = %x\n", a);
`endif
         if (a != 8'h7F) $stop;
      end
      else if (cyc == 2) begin
         b <= 128'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
         b[127] <= 1'b0;
      end
      else if (cyc == 3) begin
`ifdef TEST_VERBOSE
         $write("b = %x\n", b);
`endif
         if (b != 128'h7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) $stop;
      end
      else if (cyc > 3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
