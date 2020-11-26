// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int value;
   extern function int ext_f_np;
   extern function int ext_f_p();
   extern function int ext_f_i(int in);
   extern task ext_t_np;
   extern task ext_t_p();
   extern task ext_t_i(int in);
endclass

function int Cls::ext_f_np;
   return 1;
endfunction

function int Cls::ext_f_p();
   return value;
endfunction

function int Cls::ext_f_i(int in);
   return in+1;
endfunction

task Cls::ext_t_np();
   $write("*-* All Finished *-*\n");
endtask
task Cls::ext_t_p();
   $finish;
endtask
task Cls::ext_t_i(int in);
   if (in != 2) $stop;
   value = in;
endtask

module t (/*AUTOARG*/);
   initial begin
      Cls c = new;
      c.ext_t_i(2);
      c.ext_t_np();
      c.ext_t_p();
      if (c.ext_f_np() != 1) $stop;
      if (c.ext_f_p() != 2) $stop;
      if (c.ext_f_i(10) != 11) $stop;
   end
endmodule
