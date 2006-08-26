// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   reg [40:0] quad; initial quad = 41'ha_bbbb_cccc;
   reg [80:0] wide; initial wide = 81'habc_1234_5678_1234_5678;
   reg [31:0] str; initial str = "\000\277\021\n";
   reg [47:0] str2; initial str2 = "\000what!";
   reg [79:0] str3; initial str3 = "\000hmmm!1234";
   initial begin
      $write("[%0t] ", $time);
      $write("%m: Hi\n");

      // Display formatting
      $display("[%0t] %%X=%X %%D=%D %%0X=%0X %%0O=%0O %%B=%B", $time,
	       quad[5:0], quad[5:0], quad[5:0], quad[5:0], quad[5:0]);
      $display("[%0t] %%x=%x %%d=%d %%0x=%0x %%0o=%0o %%b=%b", $time,
	       quad[5:0], quad[5:0], quad[5:0], quad[5:0], quad[5:0]);
      $display("[%0t] %%x=%x %%0x=%0x %%o=%o %%b=%b", $time,
	       quad, quad, quad, quad);
      $display("[%0t] %%x=%x %%0x=%0x %%o=%o %%b=%b", $time,
	       wide, wide, wide, wide);
      $display;
      // Not testing %0s, it does different things in different simulators
      $display("[%0t] %%s=%s %%s=%s %%s=%s", $time,
	       str2[7:0], str2, str3);

      // Str check
`ifndef nc	// NC-Verilog 5.3 chokes on this test
      if (str !== 32'h00_bf_11_0a) $stop;
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
