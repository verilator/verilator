// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

class Cls;
   int m_index;

   function automatic int get_index();
      int rtn;
      rtn = m_index;
      ++m_index;
`ifdef VERILATOR
      return $c(rtn);  // Avoid optimizations
`else
      return rtn;
`endif
   endfunction
endclass

module t (/*AUTOARG*/);

   Cls cls;
   int array[10];

   initial begin
      cls = new;
      // Common UVM construct 'id_cnt[get_id()]++;'
      // Properly avoid/handle SIDEEFF warnings
      cls.m_index = 5;
      array[5] = 50;
      array[6] = 60;
      array[7] = 70;
      array[8] = 80;

      array[cls.get_index()]++;
      `checkd(array[5], 51);
      array[cls.get_index()]++;
      `checkd(array[6], 61);

      ++array[cls.get_index()];
      `checkd(array[7], 71);
      ++array[cls.get_index()];
      `checkd(array[8], 81);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
