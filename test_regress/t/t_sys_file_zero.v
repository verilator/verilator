// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   int i;
   int v;
   string s;
   reg [100*8:1]  letterl;

   initial begin
      // Display formatting
      $fwrite(0, "Never printed, file closed\n");
      i = $feof(0);
      if (i == 0) $stop;
      $fflush(0);
      $fclose(0);
      i = $ferror(0, letterl);
      i = $fgetc(0);
      `checkd(i, -1);
      i = $ungetc(0, 0);
      `checkd(i, -1);
      i = $fgets(letterl, 0);
      `checkd(i, 0);
      i = $fscanf(0, "%x", v);
      `checkd(i, -1);
      i = $ftell(0);
      `checkd(i, -1);
      i = $rewind(0);
      `checkd(i, -1);
      i = $fseek(0, 10, 0);
      `checkd(i, -1);

      $write("*-* All Finished *-*\n");
      $finish(0);  // Test arguments to finish
   end

endmodule
