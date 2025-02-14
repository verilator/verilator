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
   extern static function int get_1();
   extern task ext_t_np;
   extern task ext_t_p();
   extern task ext_t_i(int in);
   class SubCls;
      int value;
      extern function int ext_f_np;
      extern function int ext_f_p();
      extern function int ext_f_i(int in);
      extern static function int get_10();
      extern task ext_t_np;
      extern task ext_t_p();
      extern task ext_t_i(int in);
   endclass
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

function int Cls::get_1();
   return 1;
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

function int Cls::SubCls::ext_f_np;
   return 10;
endfunction

function int Cls::SubCls::ext_f_p();
   return value;
endfunction

function int Cls::SubCls::ext_f_i(int in);
   return in+10;
endfunction

function int Cls::SubCls::get_10();
   return 10;
endfunction

task Cls::SubCls::ext_t_np();
   $write("Cls::SubCls::ext_t_np\n");
endtask
task Cls::SubCls::ext_t_p();
   $write("Cls::SubCls::ext_t_p\n");
endtask
task Cls::SubCls::ext_t_i(int in);
   if (in != 20) $stop;
   value = in;
endtask


module t (/*AUTOARG*/);
   initial begin
      Cls c = new;
      Cls::SubCls subc = new;
      c.ext_t_i(2);
      if (c.ext_f_np() != 1) $stop;
      if (c.ext_f_p() != 2) $stop;
      if (c.ext_f_i(10) != 11) $stop;
      if (Cls::get_1() != 1) $stop;
      subc.ext_t_i(20);
      if (subc.ext_f_np() != 10) $stop;
      if (subc.ext_f_p() != 20) $stop;
      if (subc.ext_f_i(11) != 21) $stop;
      if (Cls::SubCls::get_10() != 10) $stop;
      subc.ext_t_np();
      subc.ext_t_p();
      c.ext_t_np();
      c.ext_t_p();
   end
endmodule
