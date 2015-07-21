// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

`include "verilated.v"

module t;
   `verilator_file_descriptor file;

   integer	chars;
   reg [1*8:1]	letterl;
   reg [8*8:1]	letterq;
   reg [16*8:1]	letterw;
   reg [16*8:1]	letterz;
   real		r;
   string	s;

   reg [7:0] 	v_a,v_b,v_c,v_d;
   reg [31:0] 	v_worda;
   reg [31:0] 	v_wordb;

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
      file = $fopen("obj_dir/t_sys_file_autoflush/t_sys_file_autoflush.log","w");
`else
      // The "w" is required so we get a FD not a MFD
      file = $fopen("obj_dir/t_sys_file_basic/t_sys_file_basic_test.log","w");
`endif
      if ($feof(file)) $stop;

      $fdisplay(file, "[%0t] hello v=%x", $time, 32'h12345667);
      $fwrite(file, "[%0t] %s\n", $time, "Hello2");
      $fflush(file);

      $fclose(file);
`ifdef verilator
      if (file != 0) $stop(1);  // Also test arguments to stop
      $fwrite(file, "Never printed, file closed\n");
`endif

      begin
	 // Check for opening errors
	 // The "r" is required so we get a FD not a MFD
	 file = $fopen("obj_dir/t_sys_file_basic/DOES_NOT_EXIST","r");
	 if (|file) $stop;	// Should not exist, IE must return 0
      end

      begin
	 // Check quadword access; a little strange, but it's legal to open "."
	 file = $fopen(".","r");
	 $fclose(file);
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

	 // $sscanf
	 if ($sscanf("x","")!=0) $stop;
	 if ($sscanf("z","z")!=0) $stop;

	 chars = $sscanf("blabcdefghijklmnop",
			 "%s", letterq);
	 if (`verbose) $write("c=%0d sa=%s\n", chars, letterq);
	 if (chars != 1) $stop;
	 if (letterq != "ijklmnop") $stop;

	 chars = $sscanf("xa=1f xb=12898971238912389712783490823_237904689_02348923",
			 "xa=%x xb=%x", letterq, letterw);
	 if (`verbose) $write("c=%0d xa=%x xb=%x\n", chars, letterq, letterw);
	 if (chars != 2) $stop;
	 if (letterq != 64'h1f) $stop;
	 if (letterw != 128'h38971278349082323790468902348923) $stop;

	 chars = $sscanf("ba=10      bb=110100101010010101012    note_the_two ",
			 "ba=%b bb=%b%s", letterq, letterw, letterz);
	 if (`verbose) $write("c=%0d xa=%x xb=%x z=%0s\n", chars, letterq, letterw, letterz);
	 if (chars != 3) $stop;
	 if (letterq != 64'h2) $stop;
	 if (letterw != 128'hd2a55) $stop;
	 if (letterz != {"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0","2"}) $stop;

	 chars = $sscanf("oa=23 ob=125634123615234123681236",
			 "oa=%o ob=%o", letterq, letterw);
	 if (`verbose) $write("c=%0d oa=%x ob=%x\n", chars, letterq, letterw);
	 if (chars != 2) $stop;
	 if (letterq != 64'h13) $stop;
	 if (letterw != 128'h55ce14f1a9c29e) $stop;

	 chars = $sscanf("r=0.1 d=-236123",
			 "r=%g d=%d", r, letterq);
	 if (`verbose) $write("c=%0d d=%d\n", chars, letterq);
	 if (chars != 2) $stop;
	 if (r != 0.1) $stop;
	 if (letterq != 64'hfffffffffffc65a5) $stop;

	 s = "r=0.2 d=-236124";
	 chars = $sscanf(s, "r=%g d=%d", r, letterq);
	 if (`verbose) $write("c=%0d d=%d\n", chars, letterq);
	 if (chars != 2) $stop;
	 if (r != 0.2) $stop;
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
	 chars = $fscanf(file, "%c%s", letterl, letterw);
	 if (`verbose) $write("c=%0d q=%c s=%s\n", chars, letterl, letterw);
	 if (chars != 2) $stop;
	 if (letterl != "f") $stop;
	 if (letterw != "\0\0\0\0\0redfishblah") $stop;

	 chars = $fscanf(file, "%c", letterl);
	 if (`verbose) $write("c=%0d l=%x\n", chars, letterl);
	 if (chars != 1) $stop;
	 if (letterl != "\n") $stop;

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
