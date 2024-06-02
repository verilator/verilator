// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;

class uvm_reg_field; // extends uvm_object;
   function void configure(bit overde, bit is_rand);
      if (overde) is_rand = 0;
      if (!is_rand) ;   // value.rand_mode(0);
      // See issue #4567
   endfunction
endclass

endpackage

module t(/*AUTOARG*/);

   initial begin
      uvm_pkg::uvm_reg_field c = new;
      c.configure(1, 0);
      c.configure(0, 0);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
