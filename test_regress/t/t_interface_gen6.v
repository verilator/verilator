// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// bug1001

interface intf
  #(parameter PARAM = 0)
   ();
   logic val;
endinterface

module t();

   generate
      if (1) begin
         intf #(.PARAM(2)) my_intf ();
         assign my_intf.val = '1;
      end else begin
         intf #(.PARAM(3)) my_intf ();
         assign my_intf.val = '0;
      end
   endgenerate

   generate
      begin
	 if (1) begin
            intf #(.PARAM(2)) my_intf ();
            assign my_intf.val = '1;
	 end else begin
            intf #(.PARAM(3)) my_intf ();
            assign my_intf.val = '0;
	 end
      end
   endgenerate

   generate
      begin
	 begin
	    if (1) begin
               intf #(.PARAM(2)) my_intf ();
               assign my_intf.val = '1;
	    end else begin
               intf #(.PARAM(3)) my_intf ();
               assign my_intf.val = '0;
	    end
	 end
      end
   endgenerate

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
