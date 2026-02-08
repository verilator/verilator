// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

virtual class Base;
    pure constraint raint;
endclass

class Cls extends Base;
    rand int b2;
    constraint raint { b2 == 5; }
endclass

virtual class Virt extends Base;
   // No constraint needed
endclass

module t;
   initial begin
      automatic Cls c = new;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
