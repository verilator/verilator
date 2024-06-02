// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls1;
   parameter type T = int;
endclass

class Cls2;
   localparam int P = 0;
endclass

interface class Icls1;
   localparam LP1 = 1;
endclass

interface class Icls2;
   parameter LP1 = 1;
endclass

class Cls3 implements Icls1#(2), Icls2#(0);
endclass

module t (/*AUTOARG*/);

   initial begin
      automatic Cls1#(bit) cls1 = new;
      automatic Cls2#(1) cls2 = new;
      automatic Cls3 cls3 = new;
      $stop;
   end
endmodule
