// DESCRIPTION: Verilator: Verilog Test module
//
// A test case for struct signal bit selection.
//
// This test is to check that bit selection of multi-dimensional signal inside
// of a packed struct works. Currently +: and -: blow up with packed structs.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2013 by Jie Xu.

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   typedef struct packed {
       logic [15:0] channel;
       logic [15:0] others;
   } buss_t;

   buss_t     b;

   reg [7:0]  a;
   reg [7:0]  c;
   reg [7:0]  d;

   union      packed {
      logic [31:0] [7:0] idx;
      struct 		     packed {
	 logic [15:0]      z, y, x;
	 logic [25:0] [7:0] r;
      } nam;
   } gpr;

   reg [14:0] gpr_a;

   initial begin
      b = {16'h8765,16'h4321};
      a = b[19:12];			// This works
      c = b[8+:8];			// This fails
      d = b[11-:8];			// This fails
      `checkh(a, 8'h54);
      `checkh(c, 8'h43);
      `checkh(d, 8'h32);

      gpr = 256'h12346789_abcdef12_3456789a_bcdef123_456789ab_cdef1234_56789abc_def12345;
      `checkh (gpr[255:255-14], 15'h091a);
      gpr_a = gpr.nam.z[15:1];
      `checkh (gpr_a, 15'h091a);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
