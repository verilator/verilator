// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (clk);
   input clk;

   reg [7:0] crc;

   wire [61:59] ah = crc[5:3];
   wire [61:59] bh = ~crc[4:2];
   wire [41:2] 	al = {crc,crc,crc,crc,crc};
   wire [41:2] 	bl = ~{crc[6:0],crc[6:0],crc[6:0],crc[6:0],crc[6:0],crc[6:2]};
   reg 		sel;

   wire [61:28] q = ( sel
		      ? func(ah, al)
		      : func(bh, bl));

   function [61:28] func;
      input [61:59] 	inh;
      input [41:2] 	inl;
      reg  [42:28]	func_mid;
      reg 		carry;
      begin
	 carry = &inl[27:2];
	 func_mid = {1'b0,inl[41:28]} + {14'b0, carry};
	 func[61:59] = inh + {2'b0, func_mid[42]};
	 func[58:42] = {17{func_mid[41]}};
	 func[41:28] = func_mid[41:28];
      end
   endfunction

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      //$write("%d %x\n", cyc, q);
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 sel <= ~sel;
	 crc <= {crc[6:0], ~^ {crc[7],crc[5],crc[4],crc[3]}};
	 if (cyc==1) begin
	    sel <= 1'b1;
	    crc <= 8'h12;
	 end
	 if (cyc==2) if (q!=34'h100000484) $stop;
	 if (cyc==3) if (q!=34'h37fffeddb) $stop;
	 if (cyc==4) if (q!=34'h080001212) $stop;
	 if (cyc==5) if (q!=34'h1fffff7ef) $stop;
	 if (cyc==6) if (q!=34'h200000848) $stop;
	 if (cyc==7) if (q!=34'h380001ebd) $stop;
	 if (cyc==8) if (q!=34'h07fffe161) $stop;
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
