// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Anderson Ignacio da Silva.
// SPDX-License-Identifier: CC0-1.0

package test_pkg;
   localparam [31:0] test_arr [4][4:0]
     = '{
         '{'h0000, 'h1000, 'h2000, 'h3000, 'h4000},
         '{'h0FFF, 'h1FFF, 'h2FFF, 'h3FFF, 'h4FFF},
         '{   'd0,    'd0,    'd0,    'd0,    'd0},
         '{   'd0,    'd1,    'd2,    'd3,    'd4}
         };

   typedef struct packed{
      logic [7:0] val_1;
      logic [7:0] val_2;
   } test_ret_t;
endpackage

module t import test_pkg::*; (clk);
   input clk;

   function automatic test_ret_t test_f(logic [31:0] val);
      test_ret_t temp;

      temp = test_ret_t'(0);
      for (int i=0; i<5; i++) begin
         if (val >= test_arr[0][i] && val <= test_arr[1][i]) begin
            temp.val_1 = test_arr[2][i][7:0];
            temp.val_2 = test_arr[3][i][7:0];
         end
      end
      return temp;
   endfunction

   test_ret_t temp;
   logic [31:0] random;

   int          cyc;
   bit [63:0] sum;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      random <= {17'b0, cyc[3:0], 11'b0};
      temp <= test_f(random);
`ifdef TEST_VERBOSE
      $display("rand: %h / Values -> val_1: %d / val_2: %d", random, temp.val_1, temp.val_2);
`endif
      if (cyc > 10 && cyc < 90) begin
         sum <= {48'h0, temp} ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      end
      else if (cyc == 99) begin
         $displayh(sum);
         if (sum != 64'h74d34ea7a775f994) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
