// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   typedef enum {A = 10, B = 20, C = 30} en_t;

   int m_pub = 1;
   local int m_loc = 2;
   protected int m_prot = B;
   task f_pub; endtask
   local task f_loc; endtask
   protected task f_prot; endtask
   static task s_pub; endtask
   static local task s_loc; endtask
   static protected task s_prot; endtask
   task check;
      Cls o;
      if (m_pub != 1) $stop;
      if (m_loc != 2) $stop;
      if (m_prot != 20) $stop;
      f_pub();  // Ok
      f_loc();  // Ok
      f_prot();  // Ok
      s_pub();  // Ok
      s_loc();  // Ok
      s_prot();  // Ok
      Cls::s_pub();  // Ok
      Cls::s_loc();  // Ok
      Cls::s_prot();  // Ok
   endtask
   class InnerCls;
      typedef enum {A = 10, B = 20, C = 30} en_t;

      int m_pub = 1;
      local int m_loc = 2;
      protected int m_prot = B;
      task f_pub; endtask
      local task f_loc; endtask
      protected task f_prot; endtask
      static task s_pub; endtask
      static local task s_loc; endtask
      static protected task s_prot; endtask
      task check;
         Cls o;
         if (m_pub != 1) $stop;
         if (m_loc != 2) $stop;
         if (m_prot != 20) $stop;
         f_pub();  // Ok
         f_loc();  // Ok
         f_prot();  // Ok
         s_pub();  // Ok
         s_loc();  // Ok
         s_prot();  // Ok
         Cls::s_pub();  // Ok
         Cls::s_loc();  // Ok
         Cls::s_prot();  // Ok
      endtask
   endclass
endclass

class Ext extends Cls;
   task check;
      if (m_pub != 1) $stop;
      if (m_prot != 20) $stop;
      f_pub();  // Ok
      f_prot();  // Ok
      s_pub();  // Ok
      s_prot();  // Ok
      Cls::s_pub();  // Ok
      Cls::s_prot();  // Ok
   endtask
   class ExtInner extends Cls::InnerCls;
      task check;
         if (m_pub != 1) $stop;
         if (m_prot != 20) $stop;
         f_pub();  // Ok
         f_prot();  // Ok
         s_pub();  // Ok
         s_prot();  // Ok
         Cls::InnerCls::s_pub();  // Ok
         Cls::InnerCls::s_prot();  // Ok
      endtask
   endclass
endclass

module t (/*AUTOARG*/);
   const Cls mod_c = new;
   const Cls::InnerCls imod_c = new;

   initial begin
      Cls c;
      Cls::InnerCls i;
      Ext e;
      Ext::ExtInner ei;
      if (c.A != 10) $stop;
      if (i.A != 10) $stop;
      c = new;
      i = new;
      e = new;
      ei = new;
      if (c.m_pub != 1) $stop;
      if (i.m_pub != 1) $stop;
      //
      if (mod_c.A != 10) $stop;
      if (imod_c.A != 10) $stop;
      //
      c.check();
      i.check();
      e.check();
      ei.check();
      //
      Cls::s_pub();  // Ok
      Cls::InnerCls::s_pub();  // Ok
      c.s_pub();  // Ok
      i.s_pub();  // Ok
      e.s_pub();  // Ok
      ei.s_pub();  // Ok
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
