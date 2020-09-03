// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

`define STRINGIFY(x) `"x`"

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [63:0] crc;
   integer fd;
   integer fdtmp;

   t_case_write1_tasks tasks ();

   integer cyc; initial cyc=0;

   always @ (posedge clk) begin
      $fwrite(fd, "[%0d] crc=%x ", cyc, crc);
      tasks.big_case(fd, crc[31:0]);
      $fwrite(fd, "\n");
   end

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%x\n",$time, cyc, crc);
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc==1) begin
         crc <= 64'h00000000_00000097;
         $write("%s", {"Open ", `STRINGIFY(`TEST_OBJ_DIR), "/t_case_write1_logger.log\n"});
         fdtmp = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/t_case_write1_logger.log"}, "w");
         fd <= fdtmp;
      end
      if (cyc==90) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
