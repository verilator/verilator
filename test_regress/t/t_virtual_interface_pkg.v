// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Yilou Wang.
// SPDX-License-Identifier: CC0-1.0

package my_pkg;

   virtual class CallBackBase;
      pure virtual function void add(int a, int b);
   endclass

   class my_class extends CallBackBase;
      virtual my_interface vif;

      function new(virtual my_interface vif);
         this.vif = vif;
         $display("my_class::new");
         vif.register_callback(this);
      endfunction

      function void add(int a, int b);
         // $display("a + b = %0d", a + b);
      endfunction
   endclass

endpackage

interface my_interface;
   import my_pkg::*;
   CallBackBase callback_obj;

   function void register_callback(CallBackBase obj);
      callback_obj = obj;
   endfunction

   logic clk;
   always @(posedge clk) begin
      if (callback_obj != null)
        callback_obj.add(1, 2);
      else $display("callback_obj is null");
   end
endinterface

module t;
   import my_pkg::*;
   logic clk = 0;
   my_interface vif();
   my_class cl;

   assign vif.clk = clk;

   initial begin
      forever #5 clk = ~clk;
   end

   initial begin
      #10;
      cl = new(vif);
      #100;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
