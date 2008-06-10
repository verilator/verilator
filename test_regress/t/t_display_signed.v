// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   reg signed [20:0] longp; initial longp = 21'shbbccc;
   reg signed [20:0] longn; initial longn = 21'shbbccc; initial longn[20]=1'b1;
   reg signed [40:0] quadp; initial quadp = 41'sh1_bbbb_cccc;
   reg signed [40:0] quadn; initial quadn = 41'sh1_bbbb_cccc; initial quadn[40]=1'b1;
   reg signed [80:0] widep; initial widep = 81'shbc_1234_5678_1234_5678;
   reg signed [80:0] widen; initial widen = 81'shbc_1234_5678_1234_5678; initial widen[40]=1'b1;

   initial begin
      // Display formatting
      $display("[%0t] lp %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d", $time,
	       longp, longp, longp, longp, longp, longp);
      $display("[%0t] ln %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d", $time,
	       longn, longn, longn, longn, longn, longn);
      $display("[%0t] qp %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d", $time,
	       quadp, quadp, quadp, quadp, quadp, quadp);
      $display("[%0t] qn %%x=%x %%x=%x %%o=%o %%b=%b %%0d=%0d %%d=%d", $time,
	       quadn, quadn, quadn, quadn, quadn, quadn);
      $display("[%0t] wp %%x=%x %%x=%x %%o=%o %%b=%b", $time,
	       widep, widep, widep, widep);
      $display("[%0t] wn %%x=%x %%x=%x %%o=%o %%b=%b", $time,
	       widen, widen, widen, widen);
      $display;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
