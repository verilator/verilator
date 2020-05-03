// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

virtual interface vi_t vi;
virtual vi_t vi2;

typedef class c;
typedef interface class ic;

class C #(parameter P=1);
   localparam LOCPAR = 10;
   int  imember;

   local int loc;
   protected int prot;

   rand int irand;
   randc int icrand;

   task classtask; endtask
   function int classfunc; endfunction
   virtual function void func_virtual; endfunction
   pure virtual function void func_pure_virtual;
   automatic function void func_automatic; endfunction
   const function void func_const; endfunction
   extern task exttask;
endclass

virtual class VC;
endclass

module t (/*AUTOARG*/);
endmodule
