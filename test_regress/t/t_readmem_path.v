// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;

   // verilator lint_off LITENDIAN
   reg [5:0] binary_nostart [2:15];
   // verilator lint_on LITENDIAN

   integer fd;

   initial begin

      $readmemb("t_sys_readmem_b.mem", binary_nostart);
      fd = $fopen("a_file.mem", "w");
      $fdisplay(fd, "This is a file");
      $fclose(fd);
      fd = $fopen("a_file.mem", "r");

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
