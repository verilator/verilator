// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package u_pkg;
   typedef class u_report_object;
   typedef class u_callback;

   virtual class u_object;
   endclass

   class u_queue #(type T=int) extends u_object;
      int m_value = 6;
   endclass

   class u_callbacks_base extends u_object;
      typedef u_callbacks_base this_type;
   endclass

   class u_typed_callbacks#(type T=u_object) extends u_callbacks_base;
      typedef u_typed_callbacks#(T) this_type;
      static this_type m_t_inst;
      static u_queue#(u_callback) m_tw_cb_q;
   endclass

   class u_callbacks #(type T=u_object, type CB=u_callback)
      extends u_typed_callbacks#(T);
      static function bit m_register_pair();
      endfunction
      static function void add(u_callback cb);
         u_queue#(u_callback) qr;
         qr = u_callbacks#(u_report_object,u_callback)::m_t_inst.m_tw_cb_q;  //<<<<
         if (qr.m_value != 6) $stop;
      endfunction
   endclass

   class u_callback extends u_object;
   endclass

   virtual class u_report_catcher extends u_callback;
      static local bit m_register_cb_u_report_catcher = u_callbacks#(u_report_object,u_report_catcher)::m_register_pair();
   endclass

   // Having this class (versus using #(u_object) is needed to hit the bug
   class u_report_object extends u_object;
   endclass

endpackage

module t;

   u_pkg::u_callback cb;

   initial begin
      cb = new;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
