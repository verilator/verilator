// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkg(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%g' exp='%g'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   string s;

   integer      cyc = 0;

   // Check constification
   initial begin
      s="1234"; `checkh(s.len(),4);
      s="ab7CD"; `checks(s.toupper(), "AB7CD");
      s="ab7CD"; `checks(s.tolower(), "ab7cd");
      s="1234"; s.putc(-1, "z"); `checks(s, "1234");
      s="1234"; s.putc(4, "z"); `checks(s, "1234");
      s="1234"; s.putc(2, 0); `checks(s, "1234");
      s="1234"; s.putc(2, "z"); `checks(s, "12z4");
      s="1234"; `checkh(s.getc(-1), 0);
      s="1234"; `checkh(s.getc(4), 0);
      s="1234"; `checkh(s.getc(2), "3");
      s="b"; if (s.compare("a") <= 0) $stop;
      s="b"; if (s.compare("b") != 0) $stop;
      s="b"; if (s.compare("c") >= 0) $stop;
      s="b"; if (s.compare("A") <= 0) $stop;
      s="b"; if (s.compare("B") <= 0) $stop;
      s="b"; if (s.compare("C") <= 0) $stop;
      s="B"; if (s.compare("a") >= 0) $stop;
      s="B"; if (s.compare("b") >= 0) $stop;
      s="B"; if (s.compare("c") >= 0) $stop;
      s="b"; if (s.icompare("A") < 0) $stop;
      s="b"; if (s.icompare("B") != 0) $stop;
      s="b"; if (s.icompare("C") >= 0) $stop;
      s="abcd"; `checks(s.substr(-1,1), "");
      s="abcd"; `checks(s.substr(1,0), "");
      s="abcd"; `checks(s.substr(1,4), "");
      s="abcd"; `checks(s.substr(2,3), "cd");
      s="101"; `checkh(s.atoi(), 'd101);
      s="101"; `checkh(s.atohex(), 'h101);
      s="101"; `checkh(s.atooct(), 'o101);
      s="101"; `checkh(s.atobin(), 'b101);
      s="1.23"; `checkg(s.atoreal(), 1.23);
      s.itoa(123); `checks(s, "123");
      s.hextoa(123); `checks(s, "7b");
      s.octtoa(123); `checks(s, "173");
      s.bintoa(123); `checks(s, "1111011");
      s.realtoa(1.23); `checks(s, "1.23");
      s = "bAr";
      s = s.toupper; `checks(s, "BAR");
      s = s.tolower; `checks(s, "bar");
   end

   // Check runtime
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
         // Setup
         s = "1234";
      end
      else if (cyc==1) begin
         `checkh(s.len(),4);
      end
      else if (cyc==2) begin
         s.putc(-1, "z");
      end
      else if (cyc==3) begin
         `checks(s, "1234");
         s.putc(4, "z");
      end
      else if (cyc==4) begin
         `checks(s, "1234");
         s.putc(2, 0);
      end
      else if (cyc==5) begin
         `checks(s, "1234");
         s.putc(2, "z");
      end
      else if (cyc==6) begin
         `checks(s, "12z4");
      end
      else if (cyc==7) begin
         `checkh(s.getc(-1), 0);
         `checkh(s.getc(4), 0);
         `checkh(s.getc(2), "z");
         s="ab3CD";
      end
      else if (cyc==8) begin
         `checks(s.toupper(), "AB3CD");
         `checks(s.tolower(), "ab3cd");
         s="b";
      end
      else if (cyc==9) begin
         if (s.compare("a") <= 0) $stop;
         if (s.compare("b") != 0) $stop;
         if (s.compare("c") >= 0) $stop;
         if (s.compare("A") <= 0) $stop;
         if (s.compare("B") <= 0) $stop;
         if (s.compare("C") <= 0) $stop;
         if (s.icompare("A") < 0) $stop;
         if (s.icompare("B") != 0) $stop;
         if (s.icompare("C") >= 0) $stop;
         s="abcd";
      end
      else if (cyc==10) begin
         `checks(s.substr(-1,1), "");
         `checks(s.substr(1,0), "");
         `checks(s.substr(1,4), "");
         `checks(s.substr(2,3), "cd");
         s="101";
      end
      else if (cyc==11) begin
         `checkh(s.atoi(), 'd101);
         `checkh(s.atohex(), 'h101);
         `checkh(s.atooct(), 'o101);
         `checkh(s.atobin(), 'b101);
         s="1.23";
      end
      else if (cyc==12) begin
         `checkg(s.atoreal(), 1.23);
      end
      else if (cyc==13) begin
         s.itoa(123);
      end
      else if (cyc==14) begin
         `checks(s, "123");
         s.hextoa(123);
      end
      else if (cyc==15) begin
         `checks(s, "7b");
         s.octtoa(123);
      end
      else if (cyc==16) begin
         `checks(s, "173");
         s.bintoa(123);
      end
      else if (cyc==17) begin
         `checks(s, "1111011");
         s.realtoa(1.23);
      end
      else if (cyc==18) begin
         `checks(s, "1.23");
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
