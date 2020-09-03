// DESCRIPTION: Verilator: Dotted reference that uses another dotted reference
// as the select expression
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
   genvar the_genvar;
   generate
      for (the_genvar = 0; the_genvar < 4; the_genvar++) begin: foo_loop
         foo foo_inst();
      end
   endgenerate

   bar bar_inst();

   logic x;
   assign x = foo_loop[bar_inst.THE_LP].foo_inst.y;
   //localparam N = 2;
   //assign x = foo_loop[N].foo_inst.y;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module foo();
   logic y;
endmodule

module bar();
   localparam THE_LP = 2;
endmodule
