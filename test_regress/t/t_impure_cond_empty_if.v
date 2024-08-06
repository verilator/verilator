// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class uvm_component;
   int x;
   function void set_x();
      x = 1;
   endfunction
   function new();
      if(call_set_return_false());
   endfunction
   function bit call_set_return_false;
      set_x();
      return 0;
   endfunction
endclass

module t;
   initial begin
      automatic uvm_component a = new;
      if (a.x != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
