// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// bug998

interface intf
  #(parameter PARAM = 0)
   ();
   logic val;
   function integer func (); return 5; endfunction
endinterface

module t1(intf mod_intf);
   initial begin
      $display("%m %d", mod_intf.val);
   end
endmodule

module t();
   generate
      begin : TestIf
         intf #(.PARAM(1)) my_intf [0:0] ();
         t1 t (.mod_intf(my_intf[0]));
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
