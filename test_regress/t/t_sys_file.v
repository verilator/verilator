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

   initial begin
      // Display formatting
`ifdef verilator
      if (file != 0) $stop;
      $fwrite(file, "Never printed, file closed\n");
      if (!$feof(file)) $stop;
`endif

      file = $fopen("obj_dir/t_sys_file_test.log","w");	// The "w" is required so we get a FD not a MFD
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
	 file = $fopen("obj_dir/DOES_NOT_EXIST","r");	// The "r" is required so we get a FD not a MFD
	 if (|file) $stop;	// Should not exist, IE must return 0
      end

      begin
	 // Check quadword access; a little strange, but it's legal to open "."
	 file = $fopen(".","r");
	 $fclose(file);
      end

      begin
	 // Check read functions
	 file = $fopen("t/t_sys_file_input.dat","r");
	 if ($feof(file)) $stop;

	 // $fgetc
	 if ($fgetc(file) != "h") $stop;
	 if ($fgetc(file) != "i") $stop;
	 if ($fgetc(file) != "\n") $stop;
	 
	 // $fgets
	 chars = $fgets(letterl, file);
	 $write("c=%0d l=%s\n", chars, letterl);
	 if (chars != 1) $stop;
	 if (letterl != "l") $stop;

	 chars = $fgets(letterq, file);
	 $write("c=%0d q=%x=%s", chars, letterq, letterq); // Output includes newline
	 if (chars != 5) $stop;
	 if (letterq != "\0\0\0quad\n") $stop;

	 letterw = "5432109876543210";
	 chars = $fgets(letterw, file);
	 $write("c=%0d w=%s", chars, letterw); // Output includes newline
	 if (chars != 10) $stop;
	 if (letterw != "\0\0\0\0\0\0widestuff\n") $stop;

	 $fclose(file);
      end


      $write("*-* All Finished *-*\n");
      $finish(0);  // Test arguments to finish
   end
endmodule
