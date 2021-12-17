// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   wire  net_1;
   wire [7:0] net_8;
   assign net_1 = ~cyc[0];
   assign net_8 = ~cyc[1 +: 8];

   always @ (posedge clk) begin
      $display("%d pre : %x %x", cyc, net_8, net_1);

      case (cyc)
        4: begin
           `checkh (net_1, 0);
           `checkh (net_8, ~cyc[1 +: 8]);
        end
        5: begin
           `checkh (net_1, 0);
           `checkh (net_8, 8'h5f);
        end
        6: begin
           `checkh (net_1, 1);
           `checkh (net_8, 8'h5f);
        end
        7, 8: begin
           `checkh (net_1, 1);
           `checkh (net_8, 8'hf5);
        end
        9: begin
           `checkh (net_1, ~cyc[0]);
           `checkh (net_8, 8'hf5);
        end
        11, 12: begin
           `checkh (net_1, 1);
           `checkh (net_8, 8'h5a);
        end
        13, 14: begin
           `checkh (net_1, 0);
           `checkh (net_8, 8'ha5);
        end
        default: begin
           `checkh ({net_8, net_1}, ~cyc[0 +: 9]);
        end
      endcase

`ifndef REVERSE
      if (cyc == 3) force net_1 = 0;
      if (cyc == 5) force net_1 = 1;
      if (cyc == 8) release net_1;

      if (cyc == 4) force net_8 = 8'h5f;
      if (cyc == 6) force net_8 = 8'hf5;
      if (cyc == 9) release net_8;

      if (cyc == 10) force {net_1, net_8} = 9'b1_0101_1010;
      if (cyc == 12) force {net_8, net_1} = 9'b1010_0101_0;
      if (cyc == 14) release {net_1, net_8};
`else
      if (cyc == 8) release net_1;
      if (cyc == 5) force net_1 = 1;
      if (cyc == 3) force net_1 = 0;

      if (cyc == 9) release net_8;
      if (cyc == 6) force net_8 = 8'hf5;
      if (cyc == 4) force net_8 = 8'h5f;

      if (cyc == 14) release {net_1, net_8};
      if (cyc == 12) force {net_8, net_1} = 9'b1010_0101_0;
      if (cyc == 10) force {net_1, net_8} = 9'b1_0101_1010;
`endif

      $display("%d post: %x %x", cyc, net_8, net_1);

      case (cyc)
        3: begin
           `checkh (net_1, 0);
           `checkh (net_8, ~cyc[1 +: 8]);
        end
        4: begin
           `checkh (net_1, 0);
           `checkh (net_8, 8'h5f);
        end
        5: begin
           `checkh (net_1, 1);
           `checkh (net_8, 8'h5f);
        end
        6, 7: begin
           `checkh (net_1, 1);
           `checkh (net_8, 8'hf5);
        end
        8: begin
           `checkh (net_1, ~cyc[0]);
           `checkh (net_8, 8'hf5);
        end
        10, 11: begin
           `checkh (net_1, 1);
           `checkh (net_8, 8'h5a);
        end
        12, 13: begin
           `checkh (net_1, 0);
           `checkh (net_8, 8'ha5);
        end
        default: begin
           `checkh ({net_8, net_1}, ~cyc[0 +: 9]);
        end
      endcase

      if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
