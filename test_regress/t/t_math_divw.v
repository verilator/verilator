// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // verilator lint_off WIDTH

   //============================================================

   reg   bad;
   initial begin
      bad=0;
      c96(96'h0_0000_0000_0000_0000,	96'h8_8888_8888_8888_8888,	96'h0_0000_0000_0000_0000,	96'h0);
      c96(96'h8_8888_8888_8888_8888,	96'h0_0000_0000_0000_0000,	96'h0_0000_0000_0000_0000,	96'h0);
      c96(96'h8_8888_8888_8888_8888,	96'h0_0000_0000_0000_0002,	96'h4_4444_4444_4444_4444,	96'h0);
      c96(96'h8_8888_8888_8888_8888,	96'h0_2000_0000_0000_0000,	96'h0_0000_0000_0000_0044,	96'h0_0888_8888_8888_8888);
      c96(96'h8_8888_8888_8888_8888,	96'h8_8888_8888_8888_8888,	96'h0_0000_0000_0000_0001,	96'h0);
      c96(96'h8_8888_8888_8888_8888,	96'h8_8888_8888_8888_8889,	96'h0_0000_0000_0000_0000,	96'h8_8888_8888_8888_8888);
      c96(96'h1_0000_0000_8eba_434a,	96'h0_0000_0000_0000_0001,	96'h1_0000_0000_8eba_434a,	96'h0);

      c96(96'h0003,			96'h0002,			96'h0001,			96'h0001);
      c96(96'h0003,			96'h0003,			96'h0001,			96'h0000);
      c96(96'h0003,			96'h0004,			96'h0000,			96'h0003);
      c96(96'h0000,			96'hffff,			96'h0000,			96'h0000);
      c96(96'hffff,			96'h0001,			96'hffff,			96'h0000);
      c96(96'hffff,			96'hffff,			96'h0001,			96'h0000);
      c96(96'hffff,			96'h0003,			96'h5555,			96'h0000);
      c96(96'hffff_ffff,		96'h0001,			96'hffff_ffff,			96'h0000);
      c96(96'hffff_ffff,		96'hffff,			96'h0001_0001,			96'h0000);
      c96(96'hfffe_ffff,		96'hffff,			96'h0000_ffff,			96'hfffe);
      c96(96'h1234_5678,		96'h9abc,			96'h0000_1e1e,			96'h2c70);
      c96(96'h0000_0000,		96'h0001_0000,			96'h0000,			96'h0000_0000);
      c96(96'h0007_0000,		96'h0003_0000,			96'h0002,			96'h0001_0000);
      c96(96'h0007_0005,		96'h0003_0000,			96'h0002,			96'h0001_0005);
      c96(96'h0006_0000,		96'h0002_0000,			96'h0003,			96'h0000_0000);
      c96(96'h8000_0001,		96'h4000_7000,			96'h0001,			96'h3fff_9001);
      c96(96'hbcde_789a,		96'hbcde_789a,			96'h0001,			96'h0000_0000);
      c96(96'hbcde_789b,		96'hbcde_789a,			96'h0001,			96'h0000_0001);
      c96(96'hbcde_7899,		96'hbcde_789a,			96'h0000,			96'hbcde_7899);
      c96(96'hffff_ffff,		96'hffff_ffff,			96'h0001,			96'h0000_0000);
      c96(96'hffff_ffff,		96'h0001_0000,			96'hffff,			96'h0000_ffff);
      c96(96'h0123_4567_89ab,		96'h0001_0000,			96'h0123_4567,			96'h0000_89ab);
      c96(96'h8000_fffe_0000,		96'h8000_ffff,			96'h0000_ffff,			96'h7fff_ffff);
      c96(96'h8000_0000_0003,		96'h2000_0000_0001,		96'h0003,			96'h2000_0000_0000);

      c96(96'hffff_ffff_0000_0000,	96'h0001_0000_0000,		96'hffff_ffff,			96'h0000_0000_0000);
      c96(96'hffff_ffff_0000_0000,	96'hffff_0000_0000,		96'h0001_0001,			96'h0000_0000_0000);
      c96(96'hfffe_ffff_0000_0000,	96'hffff_0000_0000,		96'h0000_ffff,			96'hfffe_0000_0000);
      c96(96'h1234_5678_0000_0000,	96'h9abc_0000_0000,		96'h0000_1e1e,			96'h2c70_0000_0000);

      c96(96'h0000_0000_0000_0000,	96'h0001_0000_0000_0000,	96'h0000,			96'h0000_0000_0000_0000);
      c96(96'h0007_0000_0000_0000,	96'h0003_0000_0000_0000,	96'h0002,			96'h0001_0000_0000_0000);
      c96(96'h0007_0005_0000_0000,	96'h0003_0000_0000_0000,	96'h0002,			96'h0001_0005_0000_0000);
      c96(96'h0006_0000_0000_0000,	96'h0002_0000_0000_0000,	96'h0003,			96'h0000_0000_0000_0000);
      c96(96'h8000_0001_0000_0000,	96'h4000_7000_0000_0000,	96'h0001,			96'h3fff_9001_0000_0000);
      c96(96'hbcde_789a_0000_0000,	96'hbcde_789a_0000_0000,	96'h0001,			96'h0000_0000_0000_0000);
      c96(96'hbcde_789b_0000_0000,	96'hbcde_789a_0000_0000,	96'h0001,			96'h0000_0001_0000_0000);
      c96(96'hbcde_7899_0000_0000,	96'hbcde_789a_0000_0000,	96'h0000,			96'hbcde_7899_0000_0000);
      c96(96'hffff_ffff_0000_0000,	96'hffff_ffff_0000_0000,	96'h0001,			96'h0000_0000_0000_0000);
      c96(96'hffff_ffff_0000_0000,	96'h0001_0000_0000_0000,	96'hffff,			96'h0000_ffff_0000_0000);
      c96(96'h7fff_8000_0000_0000,	96'h8000_0000_0001,		96'h0000_fffe,			96'h7fff_ffff_0002);
      c96(96'h8000_0000_fffe_0000,	96'h8000_0000_ffff,		96'h0000_ffff,			96'h7fff_ffff_ffff);
      c96(96'h0008_8888_8888_8888_8888,	96'h0002_0000_0000_0000,	96'h0004_4444,			96'h0000_8888_8888_8888);

      if (bad) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   task c96;
      input [95:0] u;
      input [95:0] v;
      input [95:0] expq;
      input [95:0] expr;
      c96u( u, v, expq, expr);
      c96s( u, v, expq, expr);
      c96s(-u, v,-expq,-expr);
      c96s( u,-v,-expq, expr);
      c96s(-u,-v, expq,-expr);
   endtask

   task c96u;
      input [95:0] u;
      input [95:0] v;
      input [95:0] expq;
      input [95:0] expr;
      reg [95:0]   gotq;
      reg [95:0]   gotr;
      gotq = u/v;
      gotr = u%v;
      if (gotq != expq && v!=0) begin
	 bad = 1;
      end
      if (gotr != expr && v!=0) begin
	 bad = 1;
      end
      if (bad
`ifdef TEST_VERBOSE
	  || 1
`endif
	  ) begin
	 $write(" %x /u %x = got %x exp %x  %% got %x exp %x", u,v,gotq,expq,gotr,expr);
	 // Test for v=0 to prevent Xs causing grief
	 if (gotq != expq && v!=0) $write(" BADQ");
	 if (gotr != expr && v!=0) $write(" BADR");
	 $write("\n");
      end
   endtask

   task c96s;
      input signed [95:0] u;
      input signed [95:0] v;
      input signed [95:0] expq;
      input signed [95:0] expr;
      reg signed [95:0]   gotq;
      reg signed [95:0]   gotr;
      gotq = u/v;
      gotr = u%v;
      if (gotq != expq && v!=0) begin
	 bad = 1;
      end
      if (gotr != expr && v!=0) begin
	 bad = 1;
      end
      if (bad
`ifdef TEST_VERBOSE
	  || 1
`endif
	  ) begin
	 $write(" %x /s %x = got %x exp %x  %% got %x exp %x", u,v,gotq,expq,gotr,expr);
	 // Test for v=0 to prevent Xs causing grief
	 if (gotq != expq && v!=0) $write(" BADQ");
	 if (gotr != expr && v!=0) $write(" BADR");
	 $write("\n");
      end
   endtask

endmodule
