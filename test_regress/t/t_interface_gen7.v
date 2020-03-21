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

   intf #(.PARAM(1)) my_intf [1:0] ();

   generate
      genvar the_genvar;
      begin : ia
	 for (the_genvar = 0; the_genvar < 2; the_genvar++) begin : TestIf
	    begin
               assign my_intf[the_genvar].val = '1;
               t1 t (.mod_intf(my_intf[the_genvar]));
	    end
	 end
      end
   endgenerate

   generate
      genvar the_second_genvar;
      begin : ib
	 intf #(.PARAM(1)) my_intf [1:0] ();
	 for (the_second_genvar = 0; the_second_genvar < 2; the_second_genvar++) begin : TestIf
	    begin
               assign my_intf[the_second_genvar].val = '1;
               t1 t (.mod_intf(my_intf[the_second_genvar]));
	    end
	 end
      end
   endgenerate

   generate
      genvar the_third_genvar;
      begin : ic
	 for (the_third_genvar = 0; the_third_genvar < 2; the_third_genvar++) begin : TestIf
	    begin
	       intf #(.PARAM(1)) my_intf [1:0] ();
               assign my_intf[the_third_genvar].val = '1;
               t1 t (.mod_intf(my_intf[the_third_genvar]));
	    end
	 end
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
