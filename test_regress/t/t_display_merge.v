// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   int one =
`ifdef verilator
       $c32(1)
`else
       1
`endif
       ;

   initial begin
      $display("Merge:");
      $write("This ");
      $write("should ");
      $display("merge");

      $display("Merge:");
      $write("This ", "", "should ", "", "also ");
      $display("merge");

      $display("f");
      $write(" 1=%0d a=%m 1=%0d", one, one);
      $display(" 1=%0d b=%m 1=%0d", one, one);
      $display(" pre");
      $display(" t=%0d", $time);
      $display(" t2=%0d", $time);
      $display(" post");
      $display(" t3=%0d", $time);
      $display(" t4=%0d t5=%0d", $time,$time,$time);
      $display("m");
      $display(" t=%0d t2=%0d t3=%0d t4=%0d t5=%0d", $time,$time,$time,$time,$time);
      $display(" t=%0d t2=%0d t3=%0d t4=%0d t5=%0d", $time,$time,$time,$time,$time);
      $display("mm");
      $display("");

      $write("f");
      $write(" a=%m");
      $write(" b=%m");
      $write(" pre");
      $write(" t=%0d", $time);
      $write(" t2=%0d", $time);
      $write(" post");
      $write(" t3=%0d", $time);
      $write(" t4=%0d t5=%0d", $time,$time,$time);
      $write("m");
      $write(" t=%0d t2=%0d t3=%0d t4=%0d t5=%0d", $time,$time,$time,$time,$time);
      $write(" t=%0d t2=%0d t3=%0d t4=%0d t5=%0d", $time,$time,$time,$time,$time);
      $display("mm");

      $display("very very very very very very very very very very very very very very very very very very very very very very");
      $display("very very very very very very very very very very very very very very very very very very very very very very");
      $display("very very very very very very very very very very very very very very very very very very very very very very");
      $display("very very very very very very very very very very very very very very very very very very very very very very");
      $display("very very very very very very very very very very very very very very very very very very very very very very");
      $display("very very very very very very very very very very very very very very very very very very very very very very");
      $display("very very very very very very very very very very very very very very very very very very very very very very");
      $display("%0d%0d%0d%0d%0d %0d%0d%0d%0d%0d",
               one, one, one, one, one,
               one, one, one, one, one);
      $display("%0d%0d%0d%0d%0d %0d%0d%0d%0d%0d",
               one, one, one, one, one,
               one, one, one, one, one);
      $write("\n*-* All Finished *-*\n");
      $finish;
   end
endmodule
