// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class uvm_object_wrapper;
   function string get_type_name;
      return "abcd";
   endfunction
endclass

class uvm_default_factory;
   int m_type_names[string];
   virtual function int register;
      uvm_object_wrapper obj;
      string name;
      m_type_names[(name = obj.get_type_name())] = 1;
      return m_type_names[name];
   endfunction
endclass

module t;
   initial begin
      uvm_default_factory u = new;
      if (u.register() != 1) $stop;
      #1; // Needed only visit assignments in V3Timing
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
