// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

`define stop $stop
`ifdef VERILATOR
 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`else
 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)
`endif

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [66:0] a;
   reg [66:0] b;

   wire [15:0] aui = a[15:0];
   wire [34:0] auq = a[34:0];
   wire [66:0] auw = a[66:0];
   wire [15:0] bui = b[15:0];
   wire [34:0] buq = b[34:0];
   wire [66:0] buw = b[66:0];
   wire signed [15:0] asi = a[15:0];
   wire signed [34:0] asq = a[34:0];
   wire signed [66:0] asw = a[66:0];
   wire signed [15:0] bsi = b[15:0];
   wire signed [34:0] bsq = b[34:0];
   wire signed [66:0] bsw = b[66:0];

   // verilator lint_off WIDTH
   wire [66:0]         shifted = 2 ** b[20:0];

   wire [15:0] uiii = aui ** bui;
   wire [15:0] uiiq = aui ** buq;
   wire [15:0] uiiw = aui ** buw;
   wire [15:0] uiqi = auq ** bui;
   wire [15:0] uiqq = auq ** buq;
   wire [15:0] uiqw = auq ** buw;
   wire [15:0] uiwi = auw ** bui;
   wire [15:0] uiwq = auw ** buq;
   wire [15:0] uiww = auw ** buw;
   wire [34:0] uqii = aui ** bui;
   wire [34:0] uqiq = aui ** buq;
   wire [34:0] uqiw = aui ** buw;
   wire [34:0] uqqi = auq ** bui;
   wire [34:0] uqqq = auq ** buq;
   wire [34:0] uqqw = auq ** buw;
   wire [34:0] uqwi = auw ** bui;
   wire [34:0] uqwq = auw ** buq;
   wire [34:0] uqww = auw ** buw;
   wire [66:0] uwii = aui ** bui;
   wire [66:0] uwiq = aui ** buq;
   wire [66:0] uwiw = aui ** buw;
   wire [66:0] uwqi = auq ** bui;
   wire [66:0] uwqq = auq ** buq;
   wire [66:0] uwqw = auq ** buw;
   wire [66:0] uwwi = auw ** bui;
   wire [66:0] uwwq = auw ** buq;
   wire [66:0] uwww = auw ** buw;
   wire signed [15:0] siii = asi ** bsi;
   wire signed [15:0] siiq = asi ** bsq;
   wire signed [15:0] siiw = asi ** bsw;
   wire signed [15:0] siqi = asq ** bsi;
   wire signed [15:0] siqq = asq ** bsq;
   wire signed [15:0] siqw = asq ** bsw;
   wire signed [15:0] siwi = asw ** bsi;
   wire signed [15:0] siwq = asw ** bsq;
   wire signed [15:0] siww = asw ** bsw;
   wire signed [34:0] sqii = asi ** bsi;
   wire signed [34:0] sqiq = asi ** bsq;
   wire signed [34:0] sqiw = asi ** bsw;
   wire signed [34:0] sqqi = asq ** bsi;
   wire signed [34:0] sqqq = asq ** bsq;
   wire signed [34:0] sqqw = asq ** bsw;
   wire signed [34:0] sqwi = asw ** bsi;
   wire signed [34:0] sqwq = asw ** bsq;
   wire signed [34:0] sqww = asw ** bsw;
   wire signed [66:0] swii = asi ** bsi;
   wire signed [66:0] swiq = asi ** bsq;
   wire signed [66:0] swiw = asi ** bsw;
   wire signed [66:0] swqi = asq ** bsi;
   wire signed [66:0] swqq = asq ** bsq;
   wire signed [66:0] swqw = asq ** bsw;
   wire signed [66:0] swwi = asw ** bsi;
   wire signed [66:0] swwq = asw ** bsq;
   wire signed [66:0] swww = asw ** bsw;
   // verilator lint_on WIDTH

   task checkpow(input [66:0] ures, input signed [66:0] sres);
`ifdef TEST_VERBOSE
      $write("- lastcyc%0d: %0x**%0x = %0x (exp %0x)\n", last_cyc, a, b, uwww, ures);
`endif
      // verilator lint_off WIDTH
     `checkh(uiii, ures[15:0]);
     `checkh(uiiq, ures[15:0]);
     `checkh(uiiw, ures[15:0]);
     `checkh(uiqi, ures[15:0]);
     `checkh(uiqq, ures[15:0]);
     `checkh(uiqw, ures[15:0]);
     `checkh(uiwi, ures[15:0]);
     `checkh(uiwq, ures[15:0]);
     `checkh(uiww, ures[15:0]);
     `checkh(uqii, ures[15:0]);
     `checkh(uqiq, ures[15:0]);
     `checkh(uqiw, ures[15:0]);
     `checkh(uqqi, ures[34:0]);
     `checkh(uqqq, ures[34:0]);
     `checkh(uqqw, ures[34:0]);
     `checkh(uqwi, ures[34:0]);
     `checkh(uqwq, ures[34:0]);
     `checkh(uqww, ures[34:0]);
     `checkh(uwii, ures[15:0]);
     `checkh(uwiq, ures[15:0]);
     `checkh(uwiw, ures[15:0]);
     `checkh(uwqi, ures[34:0]);
     `checkh(uwqq, ures[34:0]);
     `checkh(uwqw, ures[34:0]);
     `checkh(uwwi, ures[66:0]);
     `checkh(uwwq, ures[66:0]);
     `checkh(uwww, ures[66:0]);
`ifdef TEST_VERBOSE
      $write("- lastcyc%0d: %0d**%0d = signed %0d (exp %0d)\n", last_cyc, asw, bsw, swww, sres);
`endif
      // verilator lint_off WIDTH
     `checkh(siii, sres[15:0]);
     `checkh(siiq, sres[15:0]);
     `checkh(siiw, sres[15:0]);
     `checkh(siqi, sres[15:0]);
     `checkh(siqq, sres[15:0]);
     `checkh(siqw, sres[15:0]);
     `checkh(siwi, sres[15:0]);
     `checkh(siwq, sres[15:0]);
     `checkh(siww, sres[15:0]);
     `checkh(sqii, sres[34:0]);
     `checkh(sqiq, sres[34:0]);
     `checkh(sqiw, sres[34:0]);
     `checkh(sqqi, sres[34:0]);
     `checkh(sqqq, sres[34:0]);
     `checkh(sqqw, sres[34:0]);
     `checkh(sqwi, sres[34:0]);
     `checkh(sqwq, sres[34:0]);
     `checkh(sqww, sres[34:0]);
     `checkh(swii, sres[66:0]);
     `checkh(swiq, sres[66:0]);
     `checkh(swiw, sres[66:0]);
     `checkh(swqi, sres[66:0]);
     `checkh(swqq, sres[66:0]);
     `checkh(swqw, sres[66:0]);
     `checkh(swwi, sres[66:0]);
     `checkh(swwq, sres[66:0]);
     `checkh(swww, sres[66:0]);
      // verilator lint_on WIDTH
   endtask

`define goldoneu(vu) \
   $write("gold: u %0x**%0x: %s = %0x\n", auw, buw, `STRINGIFY(vu), vu);
`define goldones(vs) \
   $write("gold: s %0d**%0d: %s = %0d\n", asw, bsw, `STRINGIFY(vs), vs);

   task golddump();
      // verilator lint_off WIDTH
     `goldoneu(uiii);
     `goldoneu(uiiq);
     `goldoneu(uiiw);
     `goldoneu(uiqi);
     `goldoneu(uiqq);
     `goldoneu(uiqw);
     `goldoneu(uiwi);
     `goldoneu(uiwq);
     `goldoneu(uiww);
     `goldoneu(uqii);
     `goldoneu(uqiq);
     `goldoneu(uqiw);
     `goldoneu(uqqi);
     `goldoneu(uqqq);
     `goldoneu(uqqw);
     `goldoneu(uqwi);
     `goldoneu(uqwq);
     `goldoneu(uqww);
     `goldoneu(uwii);
     `goldoneu(uwiq);
     `goldoneu(uwiw);
     `goldoneu(uwqi);
     `goldoneu(uwqq);
     `goldoneu(uwqw);
     `goldoneu(uwwi);
     `goldoneu(uwwq);
     `goldoneu(uwww);
     `goldones(siii);
     `goldones(siiq);
     `goldones(siiw);
     `goldones(siqi);
     `goldones(siqq);
     `goldones(siqw);
     `goldones(siwi);
     `goldones(siwq);
     `goldones(siww);
     `goldones(sqii);
     `goldones(sqiq);
     `goldones(sqiw);
     `goldones(sqqi);
     `goldones(sqqq);
     `goldones(sqqw);
     `goldones(sqwi);
     `goldones(sqwq);
     `goldones(sqww);
     `goldones(swii);
     `goldones(swiq);
     `goldones(swiw);
     `goldones(swqi);
     `goldones(swqq);
     `goldones(swqw);
     `goldones(swwi);
     `goldones(swwq);
     `goldones(swww);
      // verilator lint_on WIDTH
   endtask

   integer cyc; initial cyc=1;
   integer last_cyc;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         last_cyc <= cyc;
`ifdef TEST_VERBOSE
         $write("- cyc%0d: %0x**%0x = sh %0x\n", cyc, a, b, shifted);
`endif
         // Constant versions
         `checkh(67'h0 ** 21'h0, 67'h1);
         `checkh(67'h1 ** 21'h0, 67'h1);
         `checkh(67'h2 ** 21'h0, 67'h1);
         `checkh(67'h0 ** 21'h1, 67'h0);
         `checkh(67'h0 ** 21'h4, 67'h0);
         `checkh(67'h1 ** 21'h31, 67'h1);
         `checkh(67'h2 ** 21'h10, 67'h10000);
         `checkh(67'd10 ** 21'h3, 67'h3e8);
         `checkh(67'h3  ** 21'h7, 67'h88b);
         `checkh(67'h0 ** 21'h0, 67'h1);
         `checkh(67'sh0 ** 21'sh0, 67'sh1);
         `checkh(67'h10 ** 21'h0, 67'h1);
`ifndef VCS
         `checkh(61'h7ab3811219 ** 21'ha6e30, 61'h01ea58c703687e81);
`endif
         if (cyc==0) begin end
         else if (cyc==1) begin a <= 67'h0; b <= 67'h0; end
         else if (cyc==2) begin a <= 67'h0; b <= 67'h3; end
         else if (cyc==3) begin a <= 67'h1; b <= 67'h31; end
         else if (cyc==4) begin a <= 67'h2; b <= 67'h10; end
         else if (cyc==5) begin a <= 67'd10; b <= 67'd3; end
         else if (cyc==6) begin a <= 67'd3; b <= 67'd7; end
         else if (cyc==7) begin a <= 67'h7ab3811219; b <= 67'ha6e30; end

         else if (cyc==10) begin a <=  67'h0; b <=  67'h0; end
         else if (cyc==11) begin a <=  67'h0; b <=  67'h1; end
         else if (cyc==12) begin a <=  67'h0; b <= -67'h1; end
         else if (cyc==13) begin a <=  67'h0; b <=  67'h2; end
         else if (cyc==14) begin a <=  67'h0; b <=  67'h3; end

         else if (cyc==20) begin a <=  67'h1; b <=  67'h0; end
         else if (cyc==21) begin a <=  67'h1; b <=  67'h1; end
         else if (cyc==22) begin a <=  67'h1; b <= -67'h1; end
         else if (cyc==23) begin a <=  67'h1; b <=  67'h2; end
         else if (cyc==24) begin a <=  67'h1; b <=  67'h3; end

         else if (cyc==30) begin a <= -67'h1; b <=  67'h0; end
         else if (cyc==31) begin a <= -67'h1; b <=  67'h1; end
         else if (cyc==32) begin a <= -67'h1; b <= -67'h1; end
         else if (cyc==33) begin a <= -67'h1; b <=  67'h2; end
         else if (cyc==34) begin a <= -67'h1; b <=  67'h3; end

         else if (cyc==40) begin a <=  67'h2; b <=  67'h0; end
         else if (cyc==41) begin a <=  67'h2; b <=  67'h1; end
         else if (cyc==42) begin a <=  67'h2; b <= -67'h1; end
         else if (cyc==43) begin a <=  67'h2; b <=  67'h2; end
         else if (cyc==44) begin a <=  67'h2; b <=  67'h3; end

         else if (cyc==50) begin a <=  67'h3; b <=  67'h0; end
         else if (cyc==51) begin a <=  67'h3; b <=  67'h1; end
         else if (cyc==52) begin a <=  67'h3; b <= -67'h1; end
         else if (cyc==53) begin a <=  67'h3; b <=  67'h2; end
         else if (cyc==54) begin a <=  67'h3; b <=  67'h3; end

         else if (cyc==60) begin a <= -67'h2; b <=  67'h0; end
         else if (cyc==61) begin a <= -67'h2; b <=  67'h1; end
         else if (cyc==62) begin a <= -67'h2; b <= -67'h1; end
         else if (cyc==63) begin a <= -67'h2; b <=  67'h2; end
         else if (cyc==64) begin a <= -67'h2; b <=  67'h3; end

         else if (cyc==99) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
      // IEEE:
      //                   op1 < -1        op1 == -1                 op1 == 0   op1 == 1   op1 > 1
      // op2 is positive   op1 ** op2   op2 is odd -> -1, even -> 1   0             1    op1 ** op2
      // op2 is zero           1                 1                    1             1        1
      // op2 is negative       0        op2 is odd -> -1, even -> 1  'x             1        0
      case (last_cyc)
        32'd10: checkpow(67'h1, 67'h1);  //  0 **  0 -> 1
        32'd11: checkpow(67'h0, 67'h0);  //  0 **  1 -> 1
        32'd12: ;  //  0 ** -1 -> x
        32'd13: checkpow(67'h0, 67'h0);  //  0 **  2 -> 0
        32'd14: checkpow(67'h0, 67'h0);  //  0 **  3 -> 0

        32'd20: checkpow(67'h1, 67'h1);  //  1 **  0 -> 1
        32'd21: checkpow(67'h1, 67'h1);  //  1 **  1 -> 1
`ifndef IVERILOG
        32'd22: checkpow(67'h1, 67'h1);  //  1 ** -1 -> 1
`endif
        32'd23: checkpow(67'h1, 67'h1);  //  1 **  2 -> 1
        32'd24: checkpow(67'h1, 67'h1);  //  1 **  3 -> 1

        32'd30: checkpow(67'h1, 67'h1);  // -1 **  0 -> 1
        32'd31: checkpow(-67'h1, -67'h1);  // -1 **  1 -> -1 if odd else 1
        32'd32: golddump();  // -1 ** -1  SEE GOLDEN
        32'd33: golddump();  // -1 **  2  SEE GOLDEN
        32'd34: golddump();  // -1 **  3  SEE GOLDEN

        32'd40: checkpow(67'h1, 67'h1);  //  2 **  0 -> 1
        32'd41: checkpow(67'h2, 67'h2);  //  2 **  1
        32'd42: checkpow(67'h0, 67'h0);  //  2 ** -1 -> 0
        32'd43: checkpow(67'h4, 67'h4);  //  2 **  2
        32'd44: checkpow(67'h8, 67'h8);  //  2 **  3

        32'd50: checkpow(67'h1, 67'h1);  //  3 **  0 -> 0
        32'd51: checkpow(67'h3, 67'h3);  //  3 **  1
        32'd52: golddump();  //  3 ** -1 -> 0  (if negative gives 0)
        32'd53: checkpow(67'h9, 67'h9);  //  3 **  2
        32'd54: checkpow(67'h1b, 67'h1b);  //  3 **  3

        32'd60: checkpow(67'h1, 67'h1);  //  -2 **  0 -> 1
        32'd61: golddump();  //  -2 **  1  SEE GOLDEN
        32'd62: golddump();  //  -2 ** -1  SEE GOLDEN
        32'd63: golddump();  //  -2 **  2  SEE GOLDEN
        32'd64: golddump();  //  -2 **  3  SEE GOLDEN
        default: ;
      endcase
      case (cyc)
        32'd00: ;
        32'd01: ;
        32'd02: `checkh(shifted, 67'h0000000000000001);
        32'd03: `checkh(shifted, 67'h0000000000000008);
        32'd04: `checkh(shifted, 67'h0002000000000000);
        32'd05: `checkh(shifted, 67'h0000000000010000);
        32'd06: `checkh(shifted, 67'h0000000000000008);
        32'd07: `checkh(shifted, 67'h0000000000000080);
        32'd08: `checkh(shifted, 67'h0000000000000000);
        32'd09: `checkh(shifted, 67'h0000000000000000);
        default: ;
      endcase
   end
endmodule
