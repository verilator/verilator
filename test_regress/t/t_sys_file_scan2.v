// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   int cfg_file, f_stat;
   reg [8*8:1] fname;
   int index;
   int count;

   initial begin
      cfg_file = $fopen("t/t_sys_file_scan2.dat", "r");

      f_stat = $fscanf(cfg_file, "%s", fname);
      `checkd(f_stat, 1);
      `checks(fname, "vec");
      f_stat = $fscanf(cfg_file, "%d", index);
      `checkd(f_stat, 1);
      `checkd(index, 6163);
      f_stat = $fscanf(cfg_file, "%d", count);
      `checkd(f_stat, 1);
      `checkd(count, 16);

      //eof
      f_stat = $fscanf(cfg_file, "%s", fname);
      `checkd(f_stat, -1);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
