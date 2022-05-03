// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t;

`define TRIES 100

   bit [6:0]  b5a;  // We use larger than [4:0] so make sure we truncate
   bit [6:0]  b5b;  // We use larger than [4:0] so make sure we truncate
   bit [6:0]  b7c;
   bit [6:0]  b7d;
   bit [59:0] b60c;
   bit [89:0] b90c;

   bit [6:0]  max_b5a;
   bit [6:0]  max_b5b;
   bit [6:0]  max_b7c;
   bit [6:0]  max_b7d;
   bit [59:0] max_b60c;
   bit [89:0] max_b90c;

   initial begin
      for (int i = 0; i < `TRIES; ++i) begin
         // verilator lint_off WIDTH
         // Optimize away extracts
         b5a = {$random}[4:0];
         b5b = {$random}[14:10];
         // Optimize away concats
         b7c = {$random, $random, $random, $random, $random, $random, $random};
         b7d = {{{$random}[0]}, {{$random}[0]}, {{$random}[0]}, {{$random}[0]}, {{$random}[0]}};
         b60c = {$random, $random, $random, $random, $random, $random, $random};
         b90c = {$random, $random, $random, $random, $random, $random, $random};
         // verilator lint_on WIDTH

         max_b5a = max_b5a | b5a;
         max_b5b = max_b5b | b5b;
         max_b7c = max_b7c | b7c;
         max_b7d = max_b7d | b7d;
         max_b60c = max_b60c | b60c;
         max_b90c = max_b90c | b90c;
      end

      `checkh(max_b5a, 7'h1f);
      `checkh(max_b5b, 7'h1f);
      `checkh(max_b7c, 7'h7f);
      `checkh(max_b7d, 7'h1f);
      `checkh(max_b60c, ~ 60'h0);
      `checkh(max_b90c, ~ 90'h0);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
