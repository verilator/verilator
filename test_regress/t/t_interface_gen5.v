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
         intf #(.PARAM(1)) my_intf ();
         assign my_intf.val = '0;
         t1 t (.mod_intf(my_intf));
//         initial $display("%0d", my_intf.func());
      end
   endgenerate

   generate
      begin
         intf #(.PARAM(1)) my_intf ();
         assign my_intf.val = '1;
         t1 t (.mod_intf(my_intf));
//         initial $display("%0d", my_intf.func());
      end
   endgenerate

   localparam LP = 1;
   logic val;

   generate begin
      if (LP) begin
         intf #(.PARAM(2)) my_intf ();
         assign my_intf.val = '1;
         assign val = my_intf.val;
      end else begin
         intf #(.PARAM(3)) my_intf ();
         assign my_intf.val = '1;
         assign val = my_intf.val;
      end
   end endgenerate

   initial begin
      $display("%0d", val);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
