// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug3806

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [65:0] idx /*verilator public*/; initial idx = 1;

   wire unlikely = idx > 200;

   typedef enum logic {UP, DOWN} dir_t;

   dir_t direction;

   always_comb direction = idx % 2 == 0 ? UP : DOWN;

   int ups;  // Make computable

   always @(posedge clk) begin
      if (idx > 100) begin
`ifdef TEST_VERBOSE
         $write("ups = %0d\n", ups);
`endif
         if (ups != 50049) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end

      if (direction == UP)
        ++ups;
      else if (direction == UP)
        ++ups;
      else
        ups += 1000;

      case (direction)
        DOWN: idx = idx+3;
        UP: idx = idx-1;
        default: begin
           // This if just gets rid of branch pred on default^
           if (unlikely == '1) begin
              $write("never\n");
           end
        end
      endcase
   end

endmodule
