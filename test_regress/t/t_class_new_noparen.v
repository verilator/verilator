// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class u_object;
   string m_name;
   function new(string name);
      m_name = name;
   endfunction
endclass

class u_cache#(type KEY_T=int, type DATA_T=int) extends u_object;
   typedef int unsigned size_t;
   int m_max_size;

   extern function new(string name="u_cache", size_t max_size = 256);
endclass

// #() not required below, see IEEE 1800-2017 8.25.1
function u_cache::new(string name="u_cache", u_cache::size_t max_size = 256);
   super.new(name);
   this.m_max_size = max_size;
endfunction

module t(/*AUTOARG*/);

   u_cache #(real, real) obj;

   initial begin
      obj = new("fred", 62);
      if (obj.m_name != "fred") $stop;
      if (obj.m_max_size != 62) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
