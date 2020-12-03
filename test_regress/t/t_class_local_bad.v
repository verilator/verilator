// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Let context messages easily know if given line is expected ok or bad
task ok;
endtask
task bad;
endtask

class Cls;
   int m_pub = 1;
   local int m_loc = 2;
   protected int m_prot = 3;
   task f_pub; endtask
   local task f_loc; endtask
   protected task f_prot; endtask
   static task s_pub; endtask
   static local task s_loc; endtask
   static protected task s_prot; endtask
   task check;
      Cls o;
      ok();  if (m_pub != 1) $stop;
      ok();  if (m_loc != 10) $stop;
      ok();  if (m_prot != 20) $stop;
      ok();  f_pub();
      ok();  f_loc();
      ok();  f_prot();
      ok();  o.f_pub();
      ok();  o.f_loc();
      ok();  o.f_prot();
      ok();  s_pub();
      ok();  s_loc();
      ok();  s_prot();
      ok();  Cls::s_pub();
      ok();  Cls::s_loc();
      ok();  Cls::s_prot();
   endtask
endclass

class Ext extends Cls;
   task check;
      Ext o;
      ok();  if (m_pub != 1) $stop;
      bad(); if (m_loc != 10) $stop;
      ok();  if (m_prot != 20) $stop;
      ok();  f_pub();
      bad(); f_loc();
      ok();  f_prot();
      ok();  o.f_pub();
      bad(); o.f_loc();
      ok();  o.f_prot();
      ok();  s_pub();
      bad(); s_loc();
      ok();  s_prot();
      ok();  Cls::s_pub();
      bad(); Cls::s_loc();
      ok();  Cls::s_prot();
   endtask
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      Ext e;
      c = new;
      e = new;
      ok();  if (c.m_pub != 1) $stop;
      bad(); if (c.m_loc != 2) $stop;
      bad(); if (c.m_prot != 20) $stop;
      ok();  if (e.m_pub != 1) $stop;
      bad(); if (e.m_loc != 2) $stop;
      bad(); if (e.m_prot != 20) $stop;
      ok();  c.f_pub();
      bad(); c.f_loc();
      bad(); c.f_prot();
      ok();  c.s_pub();
      bad(); c.s_loc();
      bad(); c.s_prot();
      ok();  Cls::s_pub();
      bad(); Cls::s_loc();
      bad(); Cls::s_prot();
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
