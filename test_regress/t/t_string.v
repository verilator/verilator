// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;

   reg [4*8:1] 	vstr;
   const string s = "a";  // Check static assignment
   string 	s2;
   string 	s3;
   reg		eq;

   // Operators == != < <= > >=  {a,b}  {a{b}}  a[b]
   // a.len, a.putc, a.getc, a.toupper, a.tolower, a.compare, a.icompare, a.substr
   // a.atoi, a.atohex, a.atooct, a.atobin, a.atoreal,
   // a.itoa, a.hextoa, a.octoa, a.bintoa, a.realtoa

   initial begin
      $sformat(vstr, "s=%s", s);
      `checks(vstr, "s=a");
      `checks(s, "a");
      `checks({s,s,s}, "aaa");
      `checks({4{s}}, "aaaa");
      // Constification
      `checkh(s == "a", 1'b1);
      `checkh(s == "b", 1'b0);
      `checkh(s != "a", 1'b0);
      `checkh(s != "b", 1'b1);
      `checkh(s >  " ", 1'b1);
      `checkh(s >  "a", 1'b0);
      `checkh(s >= "a", 1'b1);
      `checkh(s >= "b", 1'b0);
      `checkh(s <  "a", 1'b0);
      `checkh(s <  "b", 1'b1);
      `checkh(s <= " ", 1'b0);
      `checkh(s <= "a", 1'b1);
   end

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 s2 = "c0";
      end
      else if (cyc==1) begin
	 $sformat(vstr, "s2%s", s2);
	 `checks(vstr, "s2c0");
      end
      else if (cyc==2) begin
	 s3 = s2;
	 $sformat(vstr, "s2%s", s3);
	 `checks(vstr, "s2c0");
      end
      else if (cyc==3) begin
	 s2 = "a";
	 s3 = "b";
      end
      else if (cyc==4) begin
	 `checks({s2,s3}, "ab");
	 `checks({3{s3}}, "bbb");
	 `checkh(s == "a", 1'b1);
	 `checkh(s == "b", 1'b0);
	 `checkh(s != "a", 1'b0);
	 `checkh(s != "b", 1'b1);
	 `checkh(s >  " ", 1'b1);
	 `checkh(s >  "a", 1'b0);
	 `checkh(s >= "a", 1'b1);
	 `checkh(s >= "b", 1'b0);
	 `checkh(s <  "a", 1'b0);
	 `checkh(s <  "b", 1'b1);
	 `checkh(s <= " ", 1'b0);
	 `checkh(s <= "a", 1'b1);
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
