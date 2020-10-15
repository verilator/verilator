// DESCRIPTION: Verilator: Test for issue #2267
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by James Pallister.
// SPDX-License-Identifier: CC0-1.0

module mod_a;
   mod_inner u_inner;
   mod_a_mon u_a_mon;

   initial begin
      bit x;

      u_inner.x = 1;
      u_a_mon.y = 0;
      u_a_mon.accessor;

      if (u_a_mon.y != 1) begin
         $write("%%Error: Incorrect value placed in submodule\n");
         $stop;
      end

      u_inner.x = 0;
      u_a_mon.accessor;

      if (u_a_mon.y != 0) begin
         $write("%%Error: Incorrect value placed in submodule\n");
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule : mod_a

module mod_inner;
   logic x;
endmodule : mod_inner

module mod_a_mon;
   bit y;
   function void accessor;
      begin : accessor_block
         bit read_x = mod_a.u_inner.x;
         y = read_x;
      end
   endfunction
endmodule
