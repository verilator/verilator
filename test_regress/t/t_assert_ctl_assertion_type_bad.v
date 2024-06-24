// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   );

   let ON = 3;
   let OFF = 4;

   initial begin
      $assertcontrol(OFF, 255);
      assert(0);
      $assertcontrol(ON, 16);
      assert(0);
      $assertcontrol(ON, 2);
      assert(0);
      $assertcontrol(ON);
      $assertcontrol(OFF, 128);
      assert(0);
      $assertcontrol(OFF, 2);
      assert(0);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
