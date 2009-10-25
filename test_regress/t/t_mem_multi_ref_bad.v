// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/);
   reg       dimn;
   reg [1:0] dim0;
   reg [1:0] dim1 [1:0];
   reg [1:0] dim2 [1:0][1:0];
   reg	     dim0nv[1:0];

   initial begin
      dimn[1:0] = 0;		// Bad: Not ranged
      dim0[1][1] = 0;		// Bad: Not arrayed
      dim1[1][1][1] = 0;	// Bad: Not arrayed to right depth
      dim2[1][1][1] = 0;	// OK
      dim2[0 +: 1][1] = 0;	// Bad: Range on non-bits
      dim2[1 : 0][1] = 0;	// Bad: Range on non-bits
      dim2[1][1:0] = 0;		// Bad: Bitsel too soon
      dim0nv[1:0] = 0;		// Bad: Not vectored
      dim0nv[1][1] = 0;		// Bad: Not arrayed to right depth
   end

endmodule
