// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

program;
   task atask;
   endtask
   function int afunc(input int i);
      return i+1;
   endfunction
class acls;
   static int i = 10;
endclass
endprogram

program t;

   int i;

   initial begin
      atask();

      i = afunc(2);
      if (i != 3) $stop;

      if (acls::i != 10) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endprogram
