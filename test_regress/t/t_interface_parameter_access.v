// DESCRIPTION: Verilator: Interface parameter getter
//
// A test of the import parameter used with modport
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

interface test_if #(parameter integer FOO = 1);

   // Interface variable
   logic        data;

   localparam integer BAR = FOO + 1;

   // Modport
   modport mp(
              import  getFoo,
              output  data
              );

   function integer getFoo ();
      return FOO;
   endfunction

endinterface // test_if

function integer identity (input integer x);
   return x;
endfunction


module t (/*AUTOARG*/
          // Inputs
          clk
          );
   input clk;

   test_if #( .FOO (identity(5)) ) the_interface ();
   test_if #( .FOO (identity(7)) ) array_interface [1:0] ();

   testmod testmod_i (.clk (clk),
                      .intf (the_interface),
                      .intf_no_mp (the_interface),
                      .intf_array (array_interface)
                      );

   localparam THE_TOP_FOO = the_interface.FOO;
   localparam THE_TOP_FOO_BITS = $bits({the_interface.FOO, the_interface.FOO});
   localparam THE_ARRAY_FOO = array_interface[0].FOO;

   initial begin
      if (THE_TOP_FOO != 5) begin
         $display("%%Error: THE_TOP_FOO = %0d", THE_TOP_FOO);
         $stop;
      end
      if (THE_TOP_FOO_BITS != 64) begin
         $display("%%Error: THE_TOP_FOO_BITS = %0d", THE_TOP_FOO_BITS);
         $stop;
      end
      if (THE_ARRAY_FOO != 7) begin
         $display("%%Error: THE_ARRAY_FOO = %0d", THE_ARRAY_FOO);
         $stop;
      end
   end

endmodule


module testmod
  (
   input clk,
   test_if.mp intf,
   test_if intf_no_mp,
   test_if.mp intf_array [1:0]
   );

   localparam THE_FOO = intf.FOO;
   localparam THE_OTHER_FOO = intf_no_mp.FOO;
   localparam THE_ARRAY_FOO = intf_array[0].FOO;
   localparam THE_BAR = intf.BAR;
   localparam THE_OTHER_BAR = intf_no_mp.BAR;
   localparam THE_ARRAY_BAR = intf_array[0].BAR;

   always @(posedge clk) begin
      if (THE_FOO != 5) begin
         $display("%%Error: THE_FOO = %0d", THE_FOO);
         $stop;
      end
      if (THE_OTHER_FOO != 5) begin
         $display("%%Error: THE_OTHER_FOO = %0d", THE_OTHER_FOO);
         $stop;
      end
      if (THE_ARRAY_FOO != 7) begin
         $display("%%Error: THE_ARRAY_FOO = %0d", THE_ARRAY_FOO);
         $stop;
      end
      if (intf.FOO != 5) begin
         $display("%%Error: intf.FOO = %0d", intf.FOO);
         $stop;
      end
      if (intf_no_mp.FOO != 5) begin
         $display("%%Error: intf_no_mp.FOO = %0d", intf_no_mp.FOO);
         $stop;
      end
      if (intf_array[0].FOO != 7) begin
         $display("%%Error: intf_array[0].FOO = %0d", intf_array[0].FOO);
         $stop;
      end
      //      if (i.getFoo() != 5) begin
      //         $display("%%Error: i.getFoo() = %0d", i.getFoo());
      //         $stop;
      //      end
      if (THE_BAR != 6) begin
         $display("%%Error: THE_BAR = %0d", THE_BAR);
         $stop;
      end
      if (THE_OTHER_BAR != 6) begin
         $display("%%Error: THE_OTHER_BAR = %0d", THE_OTHER_BAR);
         $stop;
      end
      if (THE_ARRAY_BAR != 8) begin
         $display("%%Error: THE_ARRAY_BAR = %0d", THE_ARRAY_BAR);
         $stop;
      end
      if (intf.BAR != 6) begin
         $display("%%Error: intf.BAR = %0d", intf.BAR);
         $stop;
      end
      if (intf_no_mp.BAR != 6) begin
         $display("%%Error: intf_no_mp.BAR = %0d", intf_no_mp.BAR);
         $stop;
      end
      if (intf_array[0].BAR != 8) begin
         $display("%%Error: intf_array[0].BAR = %0d", intf_array[0].BAR);
         $stop;
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
