// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef WRITEMEM_BIN
 `define READMEMX  $readmemb
 `define WRITEMEMX $writememb
`else
 `define READMEMX  $readmemh
 `define WRITEMEMX $writememh
`endif

module t;

   // verilator lint_off LITENDIAN
   reg [5:0] binary_string [2:15];
   reg [5:0] binary_nostart [2:15];
   reg [5:0] binary_start [0:15];
   reg [175:0] hex [0:15];
   reg [(32*6)-1:0] hex_align [0:15];
   string fns;

`ifdef WRITEMEM_READ_BACK
   reg [5:0] binary_string_tmp [2:15];
   reg [5:0] binary_nostart_tmp [2:15];
   reg [5:0] binary_start_tmp [0:15];
   reg [175:0] hex_tmp [0:15];
   reg [(32*6)-1:0] hex_align_tmp [0:15];
   string fns_tmp;
`endif
   // verilator lint_on LITENDIAN

   integer   i;

   initial begin
      begin
         // Initialize memories to zero,
         // avoid differences between 2-state and 4-state.
         for (i=0; i<16; i=i+1) begin
            binary_start[i] = 6'h0;
            hex[i] = 176'h0;
            hex_align[i] = {32*6{1'b0}};
`ifdef WRITEMEM_READ_BACK
            binary_start_tmp[i] = 6'h0;
            hex_tmp[i] = 176'h0;
            hex_align_tmp[i] = {32*6{1'b0}};
`endif
         end
         for (i=2; i<16; i=i+1) begin
            binary_string[i] = 6'h0;
            binary_nostart[i] = 6'h0;
`ifdef WRITEMEM_READ_BACK
            binary_string_tmp[i] = 6'h0;
            binary_nostart_tmp[i] = 6'h0;
`endif
         end
      end

      begin
`ifdef WRITEMEM_READ_BACK
         $readmemb("t/t_sys_readmem_b.mem", binary_nostart_tmp);
         // Do a round-trip $writememh(b) and $readmemh(b) cycle.
         // This covers $writememh and ensures we can read our
         // own memh output file.
         // If WRITEMEM_BIN is also defined, use $writememb and
         // $readmemb, otherwise use $writememh and $readmemh.
 `ifdef TEST_VERBOSE
         $display("-Writing %s", `OUT_TMP1);
 `endif
         `WRITEMEMX(`OUT_TMP1, binary_nostart_tmp);
         `READMEMX(`OUT_TMP1, binary_nostart);
`else
         $readmemb("t/t_sys_readmem_b.mem", binary_nostart);
`endif
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
         binary_start['h0c] = 6'h3f;  // Not in read range
         //
`ifdef WRITEMEM_READ_BACK
         $readmemb("t/t_sys_readmem_b_8.mem", binary_start_tmp, 4, 4+7);
 `ifdef TEST_VERBOSE
         $display("-Writing %s", `OUT_TMP2);
 `endif
         `WRITEMEMX(`OUT_TMP2, binary_start_tmp, 4, 4+7);
         `READMEMX(`OUT_TMP2, binary_start, 4, 4+7);
`else
         $readmemb("t/t_sys_readmem_b_8.mem", binary_start, 4, 4+7);  // 4-11
`endif
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
         //
         if (binary_start['h0c] != 6'h3f) $stop;
      end

      begin
         // The 'hex' array is a non-exact multiple of word size
         // (possible corner case)
`ifdef WRITEMEM_READ_BACK
         $readmemh("t/t_sys_readmem_h.mem", hex_tmp, 0);
 `ifdef TEST_VERBOSE
         $display("-Writing %s", `OUT_TMP3);
 `endif
         `WRITEMEMX(`OUT_TMP3, hex_tmp, 0);
         `READMEMX(`OUT_TMP3, hex, 0);
`else
         $readmemh("t/t_sys_readmem_h.mem", hex, 0);
`endif
`ifdef TEST_VERBOSE
         for (i=0; i<16; i=i+1) $write("    @%x = %x\n", i, hex[i]);
`endif
         if (hex['h04] != 176'h400437654321276543211765432107654321abcdef10) $stop;
         if (hex['h0a] != 176'h400a37654321276543211765432107654321abcdef11) $stop;
         if (hex['h0b] != 176'h400b37654321276543211765432107654321abcdef12) $stop;
         if (hex['h0c] != 176'h400c37654321276543211765432107654321abcdef13) $stop;
      end

      begin
         // The 'hex align' array is similar to 'hex', but it is an
         // exact multiple of word size -- another possible corner case.
`ifdef WRITEMEM_READ_BACK
         $readmemh("t/t_sys_readmem_align_h.mem", hex_align_tmp, 0);
 `ifdef TEST_VERBOSE
         $display("-Writing %s", `OUT_TMP4);
 `endif
         `WRITEMEMX(`OUT_TMP4, hex_align_tmp, 0);
         `READMEMX(`OUT_TMP4, hex_align, 0);
`else
         $readmemh("t/t_sys_readmem_align_h.mem", hex_align, 0);
`endif
`ifdef TEST_VERBOSE
         for (i=0; i<16; i=i+1) $write("    @%x = %x\n", i, hex_align[i]);
`endif
         if (hex_align['h04] != 192'h77554004_37654321_27654321_17654321_07654321_abcdef10) $stop;
         if (hex_align['h0a] != 192'h7755400a_37654321_27654321_17654321_07654321_abcdef11) $stop;
         if (hex_align['h0b] != 192'h7755400b_37654321_27654321_17654321_07654321_abcdef12) $stop;
         if (hex_align['h0c] != 192'h7755400c_37654321_27654321_17654321_07654321_abcdef13) $stop;
      end

      begin
         fns = "t/t_sys_readmem_b.mem";
`ifdef WRITEMEM_READ_BACK
         fns_tmp = `OUT_TMP5;
         $readmemb(fns, binary_string_tmp);
 `ifdef TEST_VERBOSE
         $display("-Writing %s", `OUT_TMP5);
 `endif
         `WRITEMEMX(fns_tmp, binary_string_tmp);
         `READMEMX(fns_tmp, binary_string);
`else
         $readmemb(fns, binary_string);
`endif
`ifdef TEST_VERBOSE
         for (i=0; i<16; i=i+1) $write("    @%x = %x\n", i, binary_string[i]);
`endif
         if (binary_string['h2] != 6'h02) $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
