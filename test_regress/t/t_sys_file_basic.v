// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "verilated.v"

`define STRINGIFY(x) `"x`"
`define ratio_error(a,b) (((a)>(b) ? ((a)-(b)) : ((b)-(a))) /(a))
`define checkr(gotv,expv) do if (`ratio_error((gotv),(expv))>0.0001) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t;
   integer file;
   integer file_a[0];

   integer      chars;
   reg [1*8:1]  letterl;
   reg [8*8:1]  letterq;
   reg signed [8*8:1] letterqs;
   reg [16*8:1] letterw;
   reg [16*8:1] letterz;
   real         r;
   string       s;
   integer      i;

   reg [7:0]    v_a,v_b,v_c,v_d;
   reg [31:0]   v_worda;
   reg [31:0]   v_wordb;

   integer v_length, v_off;

`ifdef TEST_VERBOSE
 `define verbose 1'b1
`else
 `define verbose 1'b0
`endif

   initial begin
      // Display formatting
`ifdef verilator
      if (file != 0) $stop;
      $fwrite(file, "Never printed, file closed\n");
      if (!$feof(file)) $stop;
`endif

`ifdef AUTOFLUSH
      // The "w" is required so we get a FD not a MFD
      file = $fopen({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_file_autoflush.log"},"w");
`else
      // The "w" is required so we get a FD not a MFD
      file = $fopen({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_file_basic_test.log"},"w");
`endif
      if ($feof(file)) $stop;

      $fdisplay(file, "[%0t] hello v=%x", $time, 32'h12345667);
      $fwrite(file, "[%0t] %s\n", $time, "Hello2");

      i = 12;
      $fwrite(file, "d: "); $fwrite(file, i); $fwrite(file, " "); $fdisplay(file, i);
      $fdisplay(file);
      $fwriteh(file, "h: "); $fwriteh(file, i); $fwriteh(file, " "); $fdisplayh(file, i);
      $fdisplayh(file);
      $fwriteo(file, "o: "); $fwriteo(file, i); $fwriteo(file, " "); $fdisplayo(file, i);
      $fdisplayo(file);
      $fwriteb(file, "b: "); $fwriteb(file, i); $fwriteb(file, " "); $fdisplayb(file, i);
      $fdisplayb(file);

      $fflush(file);
      $fflush();
      $fflush;

      $fclose(file);
`ifdef verilator
      if (file != 0) $stop(1);  // Also test arguments to stop
      $fwrite(file, "Never printed, file closed\n");
`endif

      begin
         // Check for opening errors
         // The "r" is required so we get a FD not a MFD
         file = $fopen("DOES_NOT_EXIST","r");
         if (|file) $stop;      // Should not exist, IE must return 0
         // Check error function
         s = "";
         i = $ferror(file, s);
         `checkh(i, 2);
         `checks(s, "No such file or directory");
      end

      begin
         // Check quadword access; a little strange, but it's legal to open "."
         // Also checks using array reference
         file_a[0] = $fopen(".","r");
         if (file_a[0] == 0) $stop;
         $fclose(file_a[0]);
      end

      begin
         // Check read functions w/string
         s = "t/t_sys_file_basic_input.dat";
         file = $fopen(s,"r");
         if ($feof(file)) $stop;
         $fclose(file);
      end

      begin
         // Check read functions
         file = $fopen("t/t_sys_file_basic_input.dat","r");
         if ($feof(file)) $stop;

         // $fgetc
         if ($fgetc(file) != "h") $stop;
         if ($fgetc(file) != "i") $stop;
         if ($fgetc(file) != "\n") $stop;

         // $ungetc
         if ($ungetc("x", file) != 0) $stop;
         if ($fgetc(file) != "x") $stop;

         // $fgets
         chars = $fgets(letterl, file);
         if (`verbose) $write("c=%0d l=%s\n", chars, letterl);
         if (chars != 1) $stop;
         if (letterl != "l") $stop;

         chars = $fgets(letterq, file);
         if (`verbose) $write("c=%0d q=%x=%s", chars, letterq, letterq); // Output includes newline
         if (chars != 5) $stop;
         if (letterq != "\0\0\0quad\n") $stop;

         letterw = "5432109876543210";
         chars = $fgets(letterw, file);
         if (`verbose) $write("c=%0d w=%s", chars, letterw); // Output includes newline
         if (chars != 10) $stop;
         if (letterw != "\0\0\0\0\0\0widestuff\n") $stop;

         s = "";
         chars = $fgets(s, file);
         if (`verbose) $write("c=%0d w=%s", chars, s); // Output includes newline
         if (chars != 7) $stop;
         if (s != "string\n") $stop;

         // $sscanf
         if ($sscanf("x","")!=0) $stop;
         if ($sscanf("z","z")!=0) $stop;

         chars = $sscanf("blabcdefghijklmnop",
                         "%s", letterq);
         if (`verbose) $write("c=%0d sa=%s\n", chars, letterq);
         if (chars != 1) $stop;
         if (letterq != "ijklmnop") $stop;

         chars = $sscanf("xa=1f ign=22 xb=12898971238912389712783490823_abcdef689_02348923",
                         "xa=%x ign=%*d xb=%x", letterq, letterw);
         if (`verbose) $write("c=%0d xa=%x xb=%x\n", chars, letterq, letterw);
         if (chars != 2) $stop;
         if (letterq != 64'h1f) $stop;
         if (letterw != 128'h389712783490823_abcdef689_02348923) $stop;

         chars = $sscanf("ba=10      bb=110100101010010101012    note_the_two ",
                         "ba=%b bb=%b%s", letterq, letterw, letterz);
         if (`verbose) $write("c=%0d xa=%x xb=%x z=%0s\n", chars, letterq, letterw, letterz);
         if (chars != 3) $stop;
         if (letterq != 64'h2) $stop;
         if (letterw != 128'hd2a55) $stop;
         if (letterz != {"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0","2"}) $stop;

         chars = $sscanf("oa=23 oi=11 ob=125634123615234123681236",
                         "oa=%o oi=%*o ob=%o", letterq, letterw);
         if (`verbose) $write("c=%0d oa=%x ob=%x\n", chars, letterq, letterw);
         if (chars != 2) $stop;
         if (letterq != 64'h13) $stop;
         if (letterw != 128'h55ce14f1a9c29e) $stop;

         chars = $sscanf("r=0.1 d=-236123",
                         "r=%g d=%d", r, letterq);
         if (`verbose) $write("c=%0d d=%d\n", chars, letterq);
         if (chars != 2) $stop;
         `checkr(r, 0.1);
         if (letterq != 64'hfffffffffffc65a5) $stop;

         chars = $sscanf("scan from string",
                         "scan %s string", s);
         if (`verbose) $write("c=%0d s=%s\n", chars, s);
         if (chars != 1) $stop;
         if (s != "from") $stop;

         // Cover quad and %e/%f
         chars = $sscanf("r=0.2",
                         "r=%e", r);
         if (`verbose) $write("c=%0d r=%e\n", chars, r);
         `checkr(r, 0.2);

         chars = $sscanf("r=0.3",
                         "r=%f", r);
         if (`verbose) $write("c=%0d r=%f\n", chars, r);
         `checkr(r, 0.3);

         s = "r=0.2 d=-236124";
         chars = $sscanf(s, "r=%g d=%d", r, letterq);
         if (`verbose) $write("c=%0d d=%d\n", chars, letterq);
         if (chars != 2) $stop;
         `checkr(r, 0.2);
         if (letterq != 64'hfffffffffffc65a4) $stop;

         // $fscanf
         if ($fscanf(file,"")!=0) $stop;

         if (!sync("*")) $stop;
         chars = $fscanf(file, "xa=%x xb=%x", letterq, letterw);
         if (`verbose) $write("c=%0d xa=%0x xb=%0x\n", chars, letterq, letterw);
         if (chars != 2) $stop;
         if (letterq != 64'h1f) $stop;
         if (letterw != 128'h23790468902348923) $stop;

         if (!sync("\n")) $stop;
         if (!sync("*")) $stop;
         chars = $fscanf(file, "ba=%b bb=%b %s", letterq, letterw, letterz);
         if (`verbose) $write("c=%0d ba=%0x bb=%0x z=%0s\n", chars, letterq, letterw, letterz);
         if (chars != 3) $stop;
         if (letterq != 64'h2) $stop;
         if (letterw != 128'hd2a55) $stop;
         if (letterz != "\0\0\0\0note_the_two") $stop;

         if (!sync("\n")) $stop;
         if (!sync("*")) $stop;
         chars = $fscanf(file, "oa=%o ob=%o", letterq, letterw);
         if (`verbose) $write("c=%0d oa=%0x ob=%0x\n", chars, letterq, letterw);
         if (chars != 2) $stop;
         if (letterq != 64'h13) $stop;
         if (letterw != 128'h1573) $stop;

         if (!sync("\n")) $stop;
         if (!sync("*")) $stop;
         chars = $fscanf(file, "d=%d", letterq);
         if (`verbose) $write("c=%0d d=%0x\n", chars, letterq);
         if (chars != 1) $stop;
         if (letterq != 64'hfffffffffffc65a5) $stop;

         if (!sync("\n")) $stop;
         if (!sync("*")) $stop;
         chars = $fscanf(file, "u=%d", letterqs);
         if (`verbose) $write("c=%0d u=%0x\n", chars, letterqs);
         if (chars != 1) $stop;
         if (letterqs != -236124) $stop;

         if (!sync("\n")) $stop;
         if (!sync("*")) $stop;
         chars = $fscanf(file, "%c%s", letterl, letterw);
         if (`verbose) $write("c=%0d q=%c s=%s\n", chars, letterl, letterw);
         if (chars != 2) $stop;
         if (letterl != "f") $stop;
         if (letterw != "\0\0\0\0\0redfishblah") $stop;

         chars = $fscanf(file, "%c", letterl);
         if (`verbose) $write("c=%0d l=%x\n", chars, letterl);
         if (chars != 1) $stop;
         if (letterl != "\n") $stop;

         chars = $fscanf(file, "%c%s not_included\n", letterl, s);
         if (`verbose) $write("c=%0d l=%s\n", chars, s);
         if (chars != 2) $stop;
         if (s != "BCD") $stop;

         // msg1229
         v_a = $fgetc(file);
         v_b = $fgetc(file);
         v_c = $fgetc(file);
         v_d = $fgetc(file);
         v_worda = { v_d, v_c, v_b, v_a };
         if (v_worda != "4321") $stop;

         v_wordb[7:0]   = $fgetc(file);
         v_wordb[15:8]  = $fgetc(file);
         v_wordb[23:16] = $fgetc(file);
         v_wordb[31:24] = $fgetc(file);
         if (v_wordb != "9876") $stop;

         if ($fgetc(file) != "\n") $stop;


        v_length = $ftell(file);
        $frewind(file);
        v_off = $ftell(file);
        if (v_off != 0) $stop;
        $fseek(file, 10, 0);
        v_off = $ftell(file);
        if (v_off != 10) $stop;
        $fseek(file, 1, 1);
        v_off = $ftell(file);
        if (v_off != 11) $stop;
        $fseek(file, -1, 1);
        v_off = $ftell(file);
        if (v_off != 10) $stop;
        $fseek(file, v_length, 0);
        v_off = $ftell(file);
        if (v_off != v_length) $stop;
        if ($fseek(file, 0, 2) != 0) $stop;
        v_off = $ftell(file);
        if (v_off < v_length) $stop;
        if ($rewind(file) != 0) $stop;
        v_off = $ftell(file);
        if (v_off != 0) $stop;

         $fclose(file);
      end

      $write("*-* All Finished *-*\n");
      $finish(0);  // Test arguments to finish
   end

   function sync;
      input [7:0] cexp;
      reg [7:0] cgot;
      begin
         cgot = $fgetc(file);
         if (`verbose) $write("sync=%x='%c'\n", cgot,cgot);
         sync = (cgot == cexp);
      end
   endfunction

endmodule
