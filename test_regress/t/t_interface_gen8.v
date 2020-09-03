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

   //intf #(.PARAM(1)) my_intf [1:0] ();
   intf #(.PARAM(1)) my_intf ();

   generate
      genvar the_genvar;
      for (the_genvar = 0; the_genvar < 2; the_genvar++) begin : TestIf
         //assign my_intf[the_genvar].val = '1;
         //t1 t (.mod_intf(my_intf[the_genvar]));
         t1 t (.mod_intf(my_intf));
      end
   endgenerate

//     t1 t (.mod_intf(my_intf[1]));

//   generate
//      begin : TestIf
//         assign my_intf[1].val = '1;
//         t1 t (.mod_intf(my_intf[1]));
//      end
//   endgenerate

//   generate
//      begin
//         assign my_intf[0].val = '1;
//         t1 t (.mod_intf(my_intf[0]));
//      end
//   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
