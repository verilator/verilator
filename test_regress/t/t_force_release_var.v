// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Geza Lore.
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

   reg        var_1 = 0;
   reg [7:0]  var_8 = 0;
   always @(posedge clk) begin
      var_1 <= cyc[0];
      var_8 <= cyc[1 +: 8];
   end

   always @ (posedge clk) begin
      $display("%d pre : %x %x", cyc, var_8, var_1);

      case (cyc)
        0: begin
           // Uninitialized
        end
        14: begin
           `checkh (var_1, 1);
           `checkh ({1'b0, var_8}, (cyc[0 +: 9] - 1) >> 1);
        end
        15: begin
           `checkh (var_1, 1);
           `checkh (var_8, 8'hf5);
        end
        16: begin
           `checkh (var_1, 0);
           `checkh (var_8, 8'hf5);
        end
        17, 18: begin
           `checkh (var_1, 0);
           `checkh (var_8, 8'h5f);
        end
        19: begin
           `checkh (var_1, ~cyc[0]);
           `checkh (var_8, 8'h5f);
        end
        21, 22: begin
           `checkh (var_1, 1);
           `checkh (var_8, 8'h5a);
        end
        23, 24: begin
           `checkh (var_1, 0);
           `checkh (var_8, 8'ha5);
        end
        default: begin
           `checkh ({var_8, var_1}, cyc[0 +: 9] - 1);
        end
      endcase

`ifndef REVERSE
      if (cyc == 13) force var_1 = 1;
      if (cyc == 15) force var_1 = 0;
      if (cyc == 18) release var_1;

      if (cyc == 14) force var_8 = 8'hf5;
      if (cyc == 16) force var_8 = 8'h5f;
      if (cyc == 19) release var_8;

      if (cyc == 20) force {var_1, var_8} = 9'b1_0101_1010;
      if (cyc == 22) force {var_8, var_1} = 9'b1010_0101_0;
      if (cyc == 24) release {var_1, var_8};
`else
      if (cyc == 18) release var_1;
      if (cyc == 15) force var_1 = 0;
      if (cyc == 13) force var_1 = 1;

      if (cyc == 19) release var_8;
      if (cyc == 16) force var_8 = 8'h5f;
      if (cyc == 14) force var_8 = 8'hf5;

      if (cyc == 24) release {var_1, var_8};
      if (cyc == 22) force {var_8, var_1} = 9'b1010_0101_0;
      if (cyc == 20) force {var_1, var_8} = 9'b1_0101_1010;
`endif

      $display("%d post: %x %x", cyc, var_8, var_1);

      case (cyc)
        0: begin
           // Uninitialized
        end
        13: begin
           `checkh (var_1, 1);
           `checkh ({1'b0, var_8}, (cyc[0 +: 9] - 1) >> 1);
        end
        14: begin
           `checkh (var_1, 1);
           `checkh (var_8, 8'hf5);
        end
        15: begin
           `checkh (var_1, 0);
           `checkh (var_8, 8'hf5);
        end
        16, 17, 18: begin
           `checkh (var_1, 0);
           `checkh (var_8, 8'h5f);
        end
        19: begin
           `checkh (var_1, ~cyc[0]);
           `checkh (var_8, 8'h5f);
        end
        20, 21: begin
           `checkh (var_1, 1);
           `checkh (var_8, 8'h5a);
        end
        22, 23, 24: begin
           `checkh (var_1, 0);
           `checkh (var_8, 8'ha5);
        end
        default: begin
           `checkh ({var_8, var_1}, cyc[0 +: 9] - 1);
        end
      endcase

      if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
