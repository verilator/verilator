// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

`include "verilated.v"

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [63:0] crc;
   `verilator_file_descriptor	  fd;

   t_case_write2_tasks tasks ();

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
	 $write("Open obj_dir/t_case_write2/t_case_write2_logger.log\n");
	 fd = $fopen("obj_dir/t_case_write2/t_case_write2_logger.log", "w");
      end
      if (cyc==90) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
