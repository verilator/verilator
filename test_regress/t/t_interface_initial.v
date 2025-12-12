// DESCRIPTION: Verilator: Test interface with multiple initial blocks
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that interfaces with multiple initial blocks don't cause
// "Duplicate declaration of member name: ''" errors when a method
// is called on the interface (which triggers VMemberMap::findMember).
// Initial blocks have empty names, so the member map should skip them.

interface my_iface;
   int value;

   // Multiple initial blocks (anonymous - have empty names)
   initial value = 0;
   initial $display("Init 1");
   initial $display("Init 2");

   // A method that can be called to trigger member map lookup
   function int get_value();
      return value;
   endfunction
endinterface

module t;
   my_iface iface();

   initial begin
      // This method call triggers VMemberMap::findMember on the interface
      if (iface.get_value() !== 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
