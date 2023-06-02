// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls_report_object;
   string m_msg;
   function string get_msg;
      return m_msg;
   endfunction
endclass

function Cls_report_object get_report_object;
   Cls_report_object c;
   c = new;
   c.m_msg = "hello";
   return c;
endfunction

module t (/*AUTOARG*/);

   string s;

   initial begin
      Cls_report_object _local_report_object;
      s = get_report_object().get_msg();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
