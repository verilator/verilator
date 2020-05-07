// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   reg [7:0] cyc; initial cyc=0;

   reg [31:0] loops;
   reg [31:0] loops2;
   integer   i;

   always @ (posedge clk) begin
      cyc <= cyc+8'd1;
      if (cyc == 8'd1) begin
	 $write("[%0t] t_loop: Running\n",$time);
	 // Unwind <
	 loops = 0;
	 loops2 = 0;
	 for (i=0; i<16; i=i+1) begin
	    loops = loops + i;		// surefire lint_off_line ASWEMB
	    loops2 = loops2 + i;	// surefire lint_off_line ASWEMB
	 end
	 if (i !== 16) $stop;
	 if (loops !== 120) $stop;
	 if (loops2 !== 120) $stop;
	 // Unwind <=
	 loops = 0;
	 for (i=0; i<=16; i=i+1) begin
	    loops = loops + 1;
	 end
	 if (i !== 17) $stop;
	 if (loops !== 17) $stop;
	 // Don't unwind breaked loops
	 loops = 0;
	 for (i=0; i<16; i=i+1) begin
	    loops = loops + 1;
	    if (i==7) i=99;	// break out of loop
	 end
	 if (loops !== 8) $stop;
	 // Don't unwind large loops!
	 loops = 0;
	 for (i=0; i<100000; i=i+1) begin
	    loops = loops + 1;
	 end
	 if (loops !== 100000) $stop;
	 // Test post-increment
	 loops = 0;
	 for (i=0; i<=16; i++) begin
	    loops = loops + 1;
	 end
	 if (i !== 17) $stop;
	 if (loops !== 17) $stop;
	 // Test pre-increment
	 loops = 0;
	 for (i=0; i<=16; ++i) begin
	    loops = loops + 1;
	 end
	 if (i !== 17) $stop;
	 if (loops !== 17) $stop;
	 // Test post-decrement
	 loops = 0;
	 for (i=16; i>=0; i--) begin
	    loops = loops + 1;
	 end
	 if (i !== -1) $stop;
	 if (loops !== 17) $stop;
	 // Test pre-decrement
	 loops = 0;
	 for (i=16; i>=0; --i) begin
	    loops = loops + 1;
	 end
	 if (i !== -1) $stop;
	 if (loops !== 17) $stop;
	 //
	 // 1800-2017 optionals init/expr/incr
	 loops = 0;
	 i = 0;
	 for (; i<10; ++i) ++loops;
	 if (loops !== 10) $stop;
	 //
	 loops = 0;
	 i = 0;
	 for (i=0; i<10; ) begin ++loops; ++i; end
	 if (loops !== 10) $stop;
	 //
	 loops = 0;
	 i = 0;
	 for (; ; ++i) begin ++loops; break; end
	 if (loops !== 1) $stop;
	 //
	 // bug1605
	 i = 1;
	 for (i=20; 0; ) ;
	 if (i != 20) $stop;
	 for (i=30; i<10; i++) ;
	 if (i != 30) $stop;
	 //
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
