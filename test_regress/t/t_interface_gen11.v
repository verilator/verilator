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

module t2(intf mod_intfs [1:0]);
    generate
    begin
        t1 t(.mod_intf(mod_intfs[0]));
    end
    endgenerate
endmodule

module t();

   intf #(.PARAM(1)) my_intf [1:0] ();

   t2 t2 (.mod_intfs(my_intf));

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
