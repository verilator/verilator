// DESCRIPTION: Verilator: Demonstrate deferred linking error messages
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

interface foo_intf;
   logic a;
endinterface

function integer the_other_func (input integer val);
   return val;
endfunction

module t (/*AUTOARG*/);

   localparam N = 4;

   foo_intf foos [N-1:0] ();
   logic [ 7 : 0 ] bar;

   // Non-constant dotted select is not allowed
   assign foos[bar].a = 1'b1;

   baz baz_inst ();

   // Unsure how to produce V3Param AstCellRef visitor errors
   //assign baz_inst.x = 1'b1;
   //assign baz_inst.N = 1'b1;
   //assign baz_inst.7 = 1'b1;
   //assign baz_inst.qux_t = 1'b1;
   //assign baz_inst.the_func = 1'b1;
   //assign baz_inst.the_lp = 1'b1;

   //assign bar.x = 1'b1;
   //assign fake_inst.x = 1'b1;
   //assign the_other_func.x = 1'b1;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module baz;
   typedef integer qux_t;

   function integer the_func (input integer val);
      return val;
   endfunction

   localparam the_lp = 5;
endmodule
