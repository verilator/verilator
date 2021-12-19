// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t (
          input wire        clk,
          input wire        rst,
          output reg [31:0] cyc
          );

   always @(posedge clk) begin
      if (rst) begin
         cyc <= 0;
      end else begin
         cyc <= cyc +1;
      end
   end

`ifdef CMT
   reg        var_1 /* verilator forceable */;
   reg [7:0]  var_8 /* verilator forceable */;
`else
   reg        var_1;
   reg [7:0]  var_8;
`endif

   always @(posedge clk) begin
      if (rst) begin
         var_1 <= 0;
         var_8 <= 0;
      end else begin
         var_1 <= cyc[0];
         var_8 <= cyc[1 +: 8];
      end
   end

   always @ (posedge clk) begin
      $display("%d: %x %x", cyc, var_8, var_1);

      if (!rst) begin
         case (cyc)
           0: begin // Reset values
              `checkh (var_1, 0);
              `checkh (var_8, 0);
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
           16, 17: begin
              `checkh (var_1, 0);
              `checkh (var_8, 8'h5f);
           end
           18: begin
              `checkh (var_1, ~cyc[0]);
              `checkh (var_8, 8'h5f);
           end
           20, 21: begin
              `checkh (var_1, 1);
              `checkh (var_8, 8'h5a);
           end
           22, 23: begin
              `checkh (var_1, 0);
              `checkh (var_8, 8'ha5);
           end
           default: begin
              `checkh ({var_8, var_1},  cyc[0 +: 9] - 1);
           end
         endcase
      end

      if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
