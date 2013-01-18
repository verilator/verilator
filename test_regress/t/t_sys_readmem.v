// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;

   // verilator lint_off LITENDIAN
   reg [5:0] binary_nostart [2:15];
   reg [5:0] binary_start [0:15];
   reg [175:0] hex [0:15];
   // verilator lint_on LITENDIAN

   integer   i;

   initial begin

      begin
	 $readmemb("t/t_sys_readmem_b.mem", binary_nostart);
`ifdef TEST_VERBOSE
	 for (i=0; i<16; i=i+1) $write("    @%x = %x\n", i, binary_nostart[i]);
`endif
	 if (binary_nostart['h2] != 6'h02) $stop;
	 if (binary_nostart['h3] != 6'h03) $stop;
	 if (binary_nostart['h4] != 6'h04) $stop;
	 if (binary_nostart['h5] != 6'h05) $stop;
	 if (binary_nostart['h6] != 6'h06) $stop;
	 if (binary_nostart['h7] != 6'h07) $stop;
	 if (binary_nostart['h8] != 6'h10) $stop;
	 if (binary_nostart['hc] != 6'h14) $stop;
	 if (binary_nostart['hd] != 6'h15) $stop;
      end

      begin
	 $readmemb("t/t_sys_readmem_b_8.mem", binary_start, 4, 4+7);
`ifdef TEST_VERBOSE
	 for (i=0; i<16; i=i+1) $write("    @%x = %x\n", i, binary_start[i]);
`endif
	 if (binary_start['h04] != 6'h10) $stop;
	 if (binary_start['h05] != 6'h11) $stop;
	 if (binary_start['h06] != 6'h12) $stop;
	 if (binary_start['h07] != 6'h13) $stop;
	 if (binary_start['h08] != 6'h14) $stop;
	 if (binary_start['h09] != 6'h15) $stop;
	 if (binary_start['h0a] != 6'h16) $stop;
	 if (binary_start['h0b] != 6'h17) $stop;
      end

      begin
	 $readmemh("t/t_sys_readmem_h.mem", hex, 0);
`ifdef TEST_VERBOSE
	 for (i=0; i<16; i=i+1) $write("    @%x = %x\n", i, hex[i]);
`endif
	 if (hex['h04] != 176'h400437654321276543211765432107654321abcdef10) $stop;
	 if (hex['h0a] != 176'h400a37654321276543211765432107654321abcdef11) $stop;
	 if (hex['h0b] != 176'h400b37654321276543211765432107654321abcdef12) $stop;
	 if (hex['h0c] != 176'h400c37654321276543211765432107654321abcdef13) $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
