// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class uvm_object;
endclass

class uvm_callback;
endclass

class uvm_callbacks #(type T=uvm_object, type CB=uvm_callback);
   bit m_registered = 1;
   virtual function bit m_is_registered(uvm_object obj, uvm_callback cb);
      if (m_is_for_me(cb) && m_am_i_a(obj)) begin
         return m_registered;
      end
   endfunction

   virtual function bit m_is_for_me(uvm_callback cb);
      CB this_cb;
      // verilator lint_off WIDTHTRUNC
      return ($cast(this_cb, cb));
      // verilator lint_on WIDTHTRUNC
   endfunction

   virtual function bit m_am_i_a(uvm_object obj);
      T this_t;
      // verilator lint_off WIDTHTRUNC
      return ($cast(this_t, obj));
      // verilator lint_on WIDTHTRUNC
   endfunction
endclass

class my_object extends uvm_object;
endclass

class my_callback extends uvm_callback;
endclass

class other_object extends uvm_object;
endclass

module t;

   initial begin
      my_object obj;
      other_object oobj;
      my_callback cb;
      uvm_callbacks#(my_object, my_callback) ucs;
      bit i;

      obj = new;
      oobj = new;
      cb = new;
      ucs = new;

      i = ucs.m_is_registered(obj, cb);
      if (i !== 1) $stop;
      i = ucs.m_is_registered(oobj, cb);
      if (i !== 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
