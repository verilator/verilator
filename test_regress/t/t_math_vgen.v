// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;
   reg 	   check; initial check = 1'b0;

   // verilator lint_off WIDTH

   //============================================================

   reg [  1:0] W0095; //=3
   reg [ 58:0] W0101; //=0000000FFFFFFFF
   always @(posedge clk) begin
      if (cyc==1) begin
	 W0095 = ((2'h3));
	 W0101 = ({27'h0,({16{(W0095)}})});
      end
   end
   always @(posedge clk) begin
      if (cyc==2) begin
	 if ((W0101) != (59'h0FFFFFFFF)) if (check) $stop;
      end
   end

   //============================================================

   reg        [  0:0] W1243; //=1
   always @(posedge clk) begin
      if (cyc==1) begin
      W1243 = ((1'h1));
      end
   end
   always @(posedge clk) begin
      if (cyc==2) begin
	 // Width violation, but still...
	 if (((-W1243) < 32'h01) != (1'h0)) if (check) $stop;
	 if (({32{W1243}} < 32'h01) != (1'h0)) if (check) $stop;
      end
   end

   //============================================================

   reg        [  0:0] W0344; //=0
   always @(posedge clk) begin
      if (cyc==1) begin
	 W0344 = 1'b0;
      end
   end
   always @(posedge clk) begin
      if (cyc==2) begin
	 if ((W0344) != (1'h0)) if (check) $stop;
	 if (({116{(((- 95'h7FFFFFFFFFFFFFFFFFFFFFFF) ^  95'h7FFFFFFFFFFFFFFFFFFFFFFF ) == ({94'h0,W0344}))}})) if (check) $stop;
      end
   end

   //============================================================

   reg        [ 63:0] W0372; //=FFFFFFFFFFFFFFFF
   reg [118:0] 	      W0420; //=7FFFFFFFFFFFFFFFFFFFFFFFFFFFFF
   reg [115:0] 	      W0421; //=00000000000000000000000000000
   always @(posedge clk) begin
      if (cyc==1) begin
	 W0372 = ({64{((1'h1))}});
	 W0421 = 116'h0;
	 W0420 = ({119{((W0372) <= (W0372))}});
      end
   end
   always @(posedge clk) begin
      if (cyc==2) begin
	 if ((W0420[(- (W0421[115:110]))]) != (1'h1)) if (check) $stop;
      end
   end

   //============================================================

   // gcc_2_96_bug
   reg        [ 31:0] W0161; //=FFFFFFFF
   reg [ 62:0] 	      W0217; //=0000000000000000
   reg [ 53:0] 	      W0219; //=00000000000000
   always @(posedge clk) begin
      if (cyc==1) begin
	 W0161 = 32'hFFFFFFFF;
	 W0217 = 63'h0;
	 W0219 = 54'h0;
      end
   end
   always @(posedge clk) begin
      if (cyc==2) begin
	 if ((W0161) != (32'hFFFFFFFF)) if (check) $stop;
	 if (((- (W0161)) & ((W0217[62:31]) & ({25'h0,(W0219[53:47])}))) != (32'h00000000)) if (check) $stop;
      end
   end

   //============================================================

   reg        [119:0] W0592; //=000000000000000000000000000000
   reg [  7:0] 	      W0593; //=70
   always @(posedge clk) begin
      if (cyc==1) begin
	 W0593 = (((8'h90)) * ((8'hFF)));
         W0592 = 120'h000000000000000000000000000000;
      end
   end
   always @(posedge clk) begin
      if (cyc==2) begin
	if (((W0592[119:9]) >> ((W0593))) != (111'h0000000000000000000000000000)) if (check) $stop;
      end
   end

   //============================================================

   reg        [127:0] WA1063                     ; //=00000000000000000000000000000001
   reg [ 34:0] 	      WA1064 /*verilator public*/; //=7FFFFFFFF
   reg [ 62:0] 	      WA1065                     ; //=0000000000000000
   reg [ 89:0] 	      WA1066 /*verilator public*/; //=00000000000000000000001
   reg [ 34:0] 	      WA1067                     ; //=7FFFFFFFF
   reg [111:0]	      WA1068;

   always @(check) begin
      WA1067 = (~ (35'h0));
      WA1066 = (90'h00000000000000000000001);
      WA1065 = (WA1066[89:27]);
      WA1064 = (WA1067);
      WA1063 = (~ ((~ (128'hffffffffffffffffffffffffffffffff)) ^ (~ (128'h00000000000000000000000000000001))));
   end
   always @(posedge clk) begin
      if (cyc==2) begin
	 if ((WA1063[(WA1064[(WA1065[((5'h04) | (5'h0))+:4])+:3])+:112]) != 112'h0) if (check) $stop;
      end
   end

   //============================================================

   reg        [127:0] WB1063                     ; //=00000000000000000000000000000001
   reg [ 34:0] 	      WB1064 /*verilator public*/; //=7FFFFFFFF
   reg [ 62:0] 	      WB1065                     ; //=0000000000000000
   reg [ 89:0] 	      WB1066 /*verilator public*/; //=00000000000000000000001
   reg [ 34:0] 	      WB1067                     ; //=7FFFFFFFF
   reg [111:0]	      WB1068;

   always @(posedge clk) begin
      if (cyc==1) begin
	 WB1067 = (~ (35'h0));
	 WB1066 = (90'h00000000000000000000001);
      end
      if (cyc==2) WB1065 <= (WB1066[89:27]);
      if (cyc==3) WB1064 <= (WB1067);
      if (cyc==4) WB1063 <= (~ ((~ (128'hffffffffffffffffffffffffffffffff)) ^ (~ (128'h00000000000000000000000000000001))));
      if (cyc==5) WB1068 <= (WB1063[(WB1064[(WB1065[((5'h04) | (5'h0))+:4])+:3])+:112]);
   end
   always @(posedge clk) begin
      if (cyc==9) begin
	 if (WB1068 != 112'h0) if (check) $stop;
	 if ((WB1063[(WB1064[(WB1065[((5'h04) | (5'h0))+:4])+:3])+:112]) != 112'h0) if (check) $stop;
      end
   end

   //============================================================

   reg signed [ 60:0] WC0064                     ; //=1FFFFFFFFFFFFFFF
   reg signed [  6:0] WC0065                     ; //=00
   reg signed [ 62:0] WC0067 /*verilator public*/; //=33250A3BFFFFFFFF

   always @(check) begin
      WC0064 = 61'sh1FFFFFFFFFFFFFFF;
      WC0065 = 7'sh0;
      if (((WC0064) >>> (WC0065)) != 61'sh1fffffffffffffff) if (check) $stop;
   end

   //============================================================

   reg signed [ 76:0] W0234                     ; //=00000000000000000000
   reg signed [  7:0] W0235 /*verilator public*/; //=B6
   always @(check) begin
      W0235 = 8'shb6;
      W0234 = ((77'sh0001ffffffffffffffff) >>> (W0235));
      if ((W0234) != 77'sh0) if (check) $stop;
   end

   //============================================================

   reg signed [ 30:0] W0146                     ; //=00000001
   always @(check) begin : Block71
      W0146 = (31'sh00000001);
      if ((W0146 >>> 6'sh3f) != 31'sh0) if (check) $stop;
   end

   //============================================================

   reg signed [ 54:0] W0857 /*verilator public*/; //=7FFFFFFFFFFFFF

   always @(check) begin : Block405
      W0857 = 55'sh7fffffffffffff;
      if ((63'sh7fffffffffffffff >>> (W0857[54:54] ? 7'sh56 : 7'sh7f)) != 63'sh7fffffffffffffff) if (check) $stop;
   end

   //============================================================

   always @(posedge clk) begin
      if ((((122'sh3ffffffffffffffd3e48e0900000001 >>> 8'shff) >>> 8'b1) ) != 122'sh3ffffffffffffffffffffffffffffff) if (check) $stop;
      if (((95'sh7fff_ffff_ffffffff_ffffffff <  95'sh4a76_3d8b_0f4e3995_1146e342)  != 1'h0)) if (check) $stop;
   end

   //============================================================

   reg signed [ 82:0] W0226                     ; //=47A4301EE3FB4133EE3DA

   always @* begin : Block144
      W0226 = 83'sh47A4301EE3FB4133EE3DA;
      if ((W0226 >>> 8'sh1a) != 83'sh7ffffff1e90c07b8fed04) if (check) $stop;
   end

   //============================================================

   reg signed [ 68:0] W0792 /*verilator public*/; //=169351569551247E0C
   reg signed [ 68:0] W0793                     ; //=1FFFFFFFFF4EB1A91A

   always @(posedge clk) begin
      W0793 <= 69'sh1f_ffffffff_4eb1a91a;
      W0792 <= (W0793 * 69'sh1F_0E989F3E_F15F509E);
      if (W0792 != 69'sh16_93515695_51247E0C) if (check) $stop;
   end

   //============================================================

   reg signed [  2:0] DW0515 /*verilator public*/; //=7

   always @(posedge clk) begin
      DW0515 <= 3'sh7;
      if ($signed({62'h0,DW0515[1'h1]}) != 63'sh0000000000000001) if (check) $stop;
   end

   //============================================================

   reg signed [ 62:0] W0753                     ; //=004E20004ED93E26
   reg        [  2:0] W0772 /*verilator public*/; //=7

   always @(posedge clk) begin
      W0753 <= 63'sh004E20004ED93E26; //(63'sh7fffffffffffffff + (63'sh464eac8c4ed93e27 & (63'sh08cf6243ffffffff)));
      W0772 <= 3'h7;
      if ((W0772[(W0753 <  63'sh0876c66a7e29fabf)]) != 1'h1) if (check) $stop;
      if ((W0772[(63'sh004E20004ED93E26 <  63'sh0876c66a7e29fabf)]) != 1'h1) if (check) $stop;
   end

   //============================================================

   reg        [ 98:0] W1027                     ; //=7FFFFFFFFFFFFFFFFFFFFFFFF
   always @(posedge clk) begin
      W1027 <= ~99'h0;
      // verilator lint_off CMPCONST
      if (((1'sb1 < (95'sh7fffffffffffffffffffffff >= 95'sh09deb904ffffffffe062d44c))) != 1'h0) if (check) $stop;
      // verilator lint_on CMPCONST
   end

   //============================================================

   reg signed [  5:0] W123_is_3f                     ; //=3F

   always @(posedge clk) begin
      W123_is_3f <= 6'sh3f;
   end
   always @(posedge clk) begin
      if (((~ ((32'sh088d1bcb) <<< W123_is_3f)) >>> 6'sh3f) != 32'shffffffff) if (check) $stop;
   end

   //============================================================

   reg signed [105:  0] W0032 /*verilator public*/; //=106'h3ff0000000100000000bd597bb1
   always @(check) begin : Block237
      W0032 = 106'sh3ff0000000100000000bd597bb1;
      if ((106'sh1ca0000000000000000b96b8dc2 / 106'sh3ff0000000100000000bd597bb1) != 106'sh3fffffffffffffffffffffffe36) if (check) $stop;
      if ((106'sh1ca0000000000000000b96b8dc2 / W0032) != 106'sh3fffffffffffffffffffffffe36) if (check) $stop;
   end

   //============================================================

   reg signed [ 83:  0] W0024                     ; //=84'h0000000000000e1fe9094
   reg signed [ 83:  0] W0025                     ; //=84'h0f66afffffffe308b3d7c
   always @(posedge clk) begin
      W0024 <= 84'h0000000000000e1fe9094;
      W0025 <= 84'h0f66afffffffe308b3d7c;
      if ((W0024 % W0025) != 84'sh0000000000000e1fe9094) if (check) $stop;
   end

   //============================================================

   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 if (cyc==18) begin
	    check <= 1'b1;
	 end
	 if (cyc==20) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
