// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   reg [40:0] quad; initial quad = 41'ha_bbbb_cccc;
   reg [80:0] wide; initial wide = 81'habc_1234_5678_1234_5678;
   reg [8:0]  nine; initial nine = 12;
   reg signed [40:0] quads; initial quads = -(41'sha_bbbb_cccc);
   reg signed [80:0] wides; initial wides = -(81'shabc_1234_5678_1234_5678);
   reg signed [8:0]  nines; initial nines = -12;
   reg [31:0] str; initial str = "\000\277\021\n";
   reg [47:0] str2; initial str2 = "\000what!";
   reg [79:0] str3; initial str3 = "\000hmmm!1234";
   int        n; initial n = 23;
   reg [7:0]  m; initial m = 24;
   string     svs = "sv-str";
   reg [31:0] regstr = "meep";

   sub sub ();
   sub2 sub2 ();

   initial begin
      $write("[%0t] In %m: Hi\n", $time);
      sub.write_m;
      sub2.write_m;

      // Escapes
      $display("[%0t] Back \\ Quote \"", $time);  // Old bug when \" last on the line.

      // Display formatting - constants
      $display("[%0t] %%b=%b %%0b=%0b  %%b=%b %%0b=%0b  %%b=%b %%0b=%0b", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%B=%B %%0B=%0B  %%B=%B %%0B=%0B  %%B=%B %%0B=%0B", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%d=%d %%0d=%0d  %%d=%d %%0d=%0d  %%d=%d %%0d=%0d", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%D=%D %%0D=%0D  %%D=%D %%0D=%0D  %%D=%D %%0D=%0D", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%h=%h %%0h=%0h  %%h=%h %%0h=%0h  %%h=%h %%0h=%0h", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%H=%H %%0H=%0H  %%H=%H %%0H=%0H  %%H=%H %%0H=%0H", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%o=%o %%0o=%0o  %%o=%o %%0o=%0o  %%o=%o %%0o=%0o", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%O=%O %%0O=%0O  %%O=%O %%0O=%0O  %%O=%O %%0O=%0o", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%x=%x %%0x=%0x  %%x=%x %%0x=%0x  %%x=%x %%0x=%0x", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%X=%X %%0X=%0X  %%X=%X %%0X=%0X  %%X=%X %%0X=%0X", $time,
               9'd12, 9'd12, 41'habbbbcccc, 41'habbbbcccc,
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);

      $display("[%0t] %%d=%d %%0d=%0d  %%d=%d %%0d=%0d  %%d=%d %%0d=%0d", $time,
               9'sd12, 9'sd12, -(41'shabbbbcccc), -(41'shabbbbcccc),
               81'habc_1234_5678_1234_5678, 81'habc_1234_5678_1234_5678);
      $display("[%0t] %%D=%D %%0D=%0D  %%D=%D %%0D=%0D  %%D=%D %%0D=%0D", $time,
               9'sd12, 9'sd12, -(41'shabbbbcccc), -(41'shabbbbcccc),
               -(81'shabc_1234_5678_1234_5678), -(81'shabc_1234_5678_1234_5678));

      // Display formatting
      $display("[%0t] %%b=%b %%0b=%0b  %%b=%b %%0b=%0b  %%b=%b %%0b=%0b", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%B=%B %%0B=%0B  %%B=%B %%0B=%0B  %%B=%B %%0B=%0B", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%d=%d %%0d=%0d  %%d=%d %%0d=%0d  %%d=%d %%0d=%0d", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%D=%D %%0D=%0D  %%D=%D %%0D=%0D  %%D=%D %%0D=%0D", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%h=%h %%0h=%0h  %%h=%h %%0h=%0h  %%h=%h %%0h=%0h", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%H=%H %%0H=%0H  %%H=%H %%0H=%0H  %%H=%H %%0H=%0H", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%o=%o %%0o=%0o  %%o=%o %%0o=%0o  %%o=%o %%0o=%0o", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%O=%O %%0O=%0O  %%O=%O %%0O=%0O  %%O=%O %%0O=%0o", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%x=%x %%0x=%0x  %%x=%x %%0x=%0x  %%x=%x %%0x=%0x", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%X=%X %%0X=%0X  %%X=%X %%0X=%0X  %%X=%X %%0X=%0X", $time,
               nine, nine, quad, quad, wide, wide);

      $display("[%0t] %%d=%d %%0d=%0d  %%d=%d %%0d=%0d  %%d=%d %%0d=%0d", $time,
               nines, nines, quads, quads, wides, wides);
      $display("[%0t] %%D=%D %%0D=%0D  %%D=%D %%0D=%0D  %%D=%D %%0D=%0D", $time,
               nines, nines, quads, quads, wides, wides);
      //
      // verilator lint_off WIDTH
      $display("[%0t] %%C=%C %%0C=%0C", $time,
               "a"+nine, "a"+nine);
      $display("[%0t] %%c=%c %%0c=%0c", $time,
               "a"+nine, "a"+nine);
      // verilator lint_on WIDTH

      $display("[%0t] %%v=%v %%0v=%0v  %%v=%v %%0v=%0v  %%v=%v %%0v=%0v <", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%V=%V %%0V=%0V  %%V=%V %%0V=%0V  %%V=%V %%0V=%0V <", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%p=%p %%0p=%0p  %%p=%p %%0p=%0p  %%p=%p %%0p=%0p", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%P=%P %%0P=%0P  %%P=%P %%0P=%0P  %%P=%P %%0P=%0P", $time,
               nine, nine, quad, quad, wide, wide);
      $display("[%0t] %%P=%P", $time,
               svs);

      $display("[%0t] %%u=%u %%0u=%0u", $time,
               {"a","b","c","d"}, {"a","b","c","d"});  // Avoid binary output
      $display("[%0t] %%U=%U %%0U=%0U", $time,
               {"a","b","c","d"}, {"a","b","c","d"});  // Avoid binary output
      // %z is tested in t_sys_sformat.v

      $display("[%0t] %%D=%D %%d=%d %%01d=%01d %%06d=%06d %%6d=%6d", $time,
               nine, nine, nine, nine, nine);
      $display("[%0t] %%t=%t %%03t=%03t %%0t=%0t", $time,
               $time, $time, $time);
      $display;
      // Not testing %0s, it does different things in different simulators
      $display("[%0t] %%s=%s %%s=%s %%s=%s", $time,
               str2[7:0], str2, str3);
      $display("[%0t] %%6s=:%6s: %%6s=:%6s: %%6s=:%6s:", $time,
               str2[7:0], str2, str3);
      $display("[%0t] %%8s=:%8s:", $time,
               svs);

      // Displays without format, must use default
      $write("d: "); $write(nine); $write(" "); $display(nine);
      $write; $display;
      $writeh("h: "); $writeh(nine); $writeh(" "); $displayh(nine);
      $writeh; $displayh;
      $writeo("o: "); $writeo(nine); $writeo(" "); $displayo(nine);
      $writeb; $displayb;
      $writeb("b: "); $writeb(nine); $writeb(" "); $displayb(nine);
      $writeo; $displayo;
      $display("%d", $signed(32'haaaaaaaa));  // -1431655766
      $display($signed(32'haaaaaaaa));  // -1431655766
      $display("%d", $unsigned(-2));  // 4294967294
      $display($unsigned(-2));  // 4294967294
      $display("%d", 32'haaaaaaaa);  // 2863311530
      $display(32'haaaaaaaa);  // 2863311530

      $display("[%0t] %s%s%s", $time,
               "hel", "lo, fr", "om a very long string. Percent %s are literally substituted in.");
      $display("hel", "lo, fr", "om a concatenated string.");
      $write("hel", "lo, fr", "om a concatenated format string [%0t].\n", $time);
      $display("extra argument: ", $time);
      $display($time,, ": pre argument",, "after");
      $display("empty: >%s<", "");
      $write("[%0t] Embedded tab '\t' and \r return\n", $time);
      $display("[%0t] Embedded\
multiline", $time);

      // Str check
`ifndef NC      // NC-Verilog 5.3 chokes on this test
      if (str !== 32'h00_bf_11_0a) $stop;
`endif

      // Padding
      $write("'%0d %2d %8d'\n", 23, 23, 23);
      $write("'%-0d %-2d %-8d'\n", 23, 23, 23);
      $write("'%0d %2d %8d'\n", n, n, n);
      $write("'%-0d %-2d %-8d'\n", n, n, n);
      $write("'%8d'\n", m);
      $write("'%-8d'\n", m);
      $write("'%8t'\n", $time);
      $write("'%-8t'\n", $time);
      $write("'%8s'\n", svs);
      $write("'%-8s'\n", svs);
      $write("'%8s'\n", regstr);
      $write("'%-8s'\n", regstr);
      $write("'%8s'\n", "beep");
      $write("'%-8s'\n", "beep");

      // $itord conversion bug, note a %d instead of proper float
      // verilator lint_off REALCVT
      $display("log10(2) = %d", $log10(100));
      // verilator lint_on REALCVT

      // unknown and high-impedance values
      $display("%d", 1'bx);
      $display("%h", 14'bx01010);
      $display("%h %o", 12'b001xxx101x01, 12'b001xxx101x01);
      $display("%d", 32'bx);
      $display("%d", 32'bz);
      $display("%d", 32'b11x11z111);
      $display("%d", 32'b11111z111);
      $display("%h", 12'b1zz1_zzzz_1x1z);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub;
   task write_m;
      begin
         $write("[%0t] In %m (%l)\n", $time);
         begin : subblock
            $write("[%0t] In %M (%L)\n", $time); // Uppercase %M test
         end
      end
   endtask
endmodule

module sub2;
   // verilator no_inline_module
   task write_m;
      begin
         $write("[%0t] In %m (%l)\n", $time);
         begin : subblock2
            $write("[%0t] In %m (%L)\n", $time);
         end
      end
   endtask
endmodule
