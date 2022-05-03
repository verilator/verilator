// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   real  r, r2;
   integer      cyc = 0;

   task check(integer line, real got, real ex);
      if (got != ex) begin
         if ((got > ex ? got - ex : ex - got) > 0.000001) begin
            $display("%%Error: Line %0d: Bad result, got=%0.99g expect=%0.99g",line,got,ex);
            $stop;
         end
      end
   endtask

   initial begin
      // Check constant propagation
      // Note $abs is not defined in SystemVerilog (as of 2012)
      check(`__LINE__, $ceil(-1.2),     -1);
      check(`__LINE__, $ceil(1.2),      2);
      check(`__LINE__, $exp(1.2),       3.3201169227365472380597566370852291584014892578125);
      check(`__LINE__, $exp(0.0),       1);
      check(`__LINE__, $exp(-1.2),      0.301194211912202136627314530414878390729427337646484375);
      check(`__LINE__, $floor(-1.2),    -2);
      check(`__LINE__, $floor(1.2),     1);
      check(`__LINE__, $ln(1.2),        0.1823215567939545922460098381634452380239963531494140625);
      //check(`__LINE__, $ln(0),        0);     // Bad value
      //check(`__LINE__, $ln(-1.2),     0);     // Bad value
      check(`__LINE__, $log10(1.2),     0.07918124604762481755226843915806966833770275115966796875);
      //check(`__LINE__, $log10(0),     0);     // Bad value
      //check(`__LINE__, $log10(-1.2),  0);
      check(`__LINE__, $pow(2.3,1.2),   2.71689843249914897427288451581262052059173583984375);
      check(`__LINE__, $pow(2.3,-1.2),  0.368066758785732861536388327294844202697277069091796875);
      //check(`__LINE__, $pow(-2.3,1.2),0);     // Bad value
      check(`__LINE__, $sqrt(1.2),      1.095445115010332148841598609578795731067657470703125);
      //check(`__LINE__, $sqrt(-1.2),   0);     // Bad value
      check(`__LINE__, ((1.5)**(1.25)), 1.660023);
      check(`__LINE__, $acos (0.2),     1.369438406);   // Arg1 is -1..1
      check(`__LINE__, $acosh(1.2),     0.622362503);
      check(`__LINE__, $asin (0.2),     0.201357920);   // Arg1 is -1..1
      check(`__LINE__, $asinh(1.2),     1.015973134);
      check(`__LINE__, $atan (0.2),     0.197395559);
      check(`__LINE__, $atan2(0.2,2.3), 0.086738338);   // Arg1 is -1..1
      check(`__LINE__, $atanh(0.2),     0.202732554);   // Arg1 is -1..1
      check(`__LINE__, $cos  (1.2),     0.362357754);
      check(`__LINE__, $cosh (1.2),     1.810655567);
      check(`__LINE__, $hypot(1.2,2.3), 2.594224354);
      check(`__LINE__, $sin  (1.2),     0.932039085);
      check(`__LINE__, $sinh (1.2),     1.509461355);
      check(`__LINE__, $tan  (1.2),     2.572151622);
      check(`__LINE__, $tanh (1.2),     0.833654607);
   end

   real sum_ceil;
   real sum_exp;
   real sum_floor;
   real sum_ln;
   real sum_log10;
   real sum_pow1;
   real sum_pow2;
   real sum_sqrt;

   real sum_acos;
   real sum_acosh;
   real sum_asin;
   real sum_asinh;
   real sum_atan;
   real sum_atan2;
   real sum_atanh;
   real sum_cos ;
   real sum_cosh;
   real sum_hypot;
   real sum_sin;
   real sum_sinh;
   real sum_tan;
   real sum_tanh;

   // Test loop
   always @ (posedge clk) begin
      r = $itor(cyc)/10.0 - 5.0;  // Crosses 0
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d r=%g s_ln=%0.12g\n", $time, cyc, r, sum_ln);
`endif
      cyc <= cyc + 1;
      if (cyc==0) begin
      end
      else if (cyc<90) begin
         // Setup
         sum_ceil       += 1.0+$ceil(r);
         sum_exp        += 1.0+$exp(r);
         sum_floor      += 1.0+$floor(r);
         if (r > 0.0) sum_ln    += 1.0+$ln(r);
         if (r > 0.0) sum_log10 += 1.0+$log10(r);
         // Pow requires if arg1<0 then arg1 integral
         sum_pow1 += 1.0+$pow(2.3,r);
         if (r >= 0.0) sum_pow2 += 1.0+$pow(r,2.3);
         if (r >= 0.0) sum_sqrt += 1.0+$sqrt(r);

         if (r>=-1.0 && r<=1.0) sum_acos  += 1.0+$acos (r);
         if (r>=1.0) sum_acosh += 1.0+$acosh(r);
         if (r>=-1.0 && r<=1.0) sum_asin  += 1.0+$asin (r);
         sum_asinh += 1.0+$asinh(r);
         sum_atan  += 1.0+$atan (r);
         if (r>=-1.0 && r<=1.0) sum_atan2 += 1.0+$atan2(r,2.3);
         if (r>=-1.0 && r<=1.0) sum_atanh += 1.0+$atanh(r);
         sum_cos   += 1.0+$cos  (r);
         sum_cosh  += 1.0+$cosh (r);
         sum_hypot += 1.0+$hypot(r,2.3);
         sum_sin   += 1.0+$sin  (r);
         sum_sinh  += 1.0+$sinh (r);
         sum_tan   += 1.0+$tan  (r);
         sum_tanh  += 1.0+$tanh (r);
      end
      else if (cyc==99) begin
         check (`__LINE__, sum_ceil,    85);
         check (`__LINE__, sum_exp,     608.06652950);
         check (`__LINE__, sum_floor,   4);
         check (`__LINE__, sum_ln,      55.830941633);
         check (`__LINE__, sum_log10,   46.309585076);
         check (`__LINE__, sum_pow1,    410.98798177);
         check (`__LINE__, sum_pow2,    321.94765689);
         check (`__LINE__, sum_sqrt,    92.269677253);
         check (`__LINE__, sum_acos,    53.986722862);
         check (`__LINE__, sum_acosh,   72.685208498);
         check (`__LINE__, sum_asin,    21);
         check (`__LINE__, sum_asinh,   67.034973416);
         check (`__LINE__, sum_atan,    75.511045389);
         check (`__LINE__, sum_atan2,   21);
         check (`__LINE__, sum_atanh,   0);
         check (`__LINE__, sum_cos,     72.042023124);
         check (`__LINE__, sum_cosh,    1054.0178222);
         check (`__LINE__, sum_hypot,   388.92858406);
         check (`__LINE__, sum_sin,     98.264184989);
         check (`__LINE__, sum_sinh,  -356.9512927);
         check (`__LINE__, sum_tan,     1.7007946043);
         check (`__LINE__, sum_tanh,    79.003199681);

         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
