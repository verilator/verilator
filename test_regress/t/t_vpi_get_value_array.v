// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Diego Roux. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VERILATOR_COMMENTS
 `define PUBLIC_FLAT_RD /*verilator public_flat_rd*/
 `define PUBLIC_FLAT_RW /*verilator public_flat_rw @(posedge clk)*/
`else
 `define PUBLIC_FLAT_RD
 `define PUBLIC_FLAT_RW
`endif

module test #(
    parameter WIDTH `PUBLIC_FLAT_RD = 32
) (input clk);

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   reg [7:0] read_bytes [0:3] `PUBLIC_FLAT_RD;
   reg [7:0] read_bytes_nonzero_index [1:4] `PUBLIC_FLAT_RD;
   reg [7:0] read_bytes_rl [3:0] `PUBLIC_FLAT_RD;

   reg [15:0] read_shorts [0:3] `PUBLIC_FLAT_RD;
   reg [31:0] read_words [0:3] `PUBLIC_FLAT_RD;
   reg [31:0] read_words_rl [3:0] `PUBLIC_FLAT_RD;
   reg [63:0] read_longs [0:3] `PUBLIC_FLAT_RD;
   integer read_integers [0:3] `PUBLIC_FLAT_RD;
   reg [68:0] read_customs [0:3] `PUBLIC_FLAT_RD;
   reg [68:0] read_customs_nonzero_index_rl [4:1] `PUBLIC_FLAT_RD;

   reg [7:0] read_scalar `PUBLIC_FLAT_RD;
   reg [7:0] read_bounds [1:3] `PUBLIC_FLAT_RD;

   integer status;

   initial begin
      read_bytes[0] = 8'had;
      read_bytes[1] = 8'hde;
      read_bytes[2] = 8'hef;
      read_bytes[3] = 8'hbe;

      read_bytes_rl[3] = 8'had;
      read_bytes_rl[2] = 8'hde;
      read_bytes_rl[1] = 8'hef;
      read_bytes_rl[0] = 8'hbe;

      read_bytes_nonzero_index[1] = 8'had;
      read_bytes_nonzero_index[2] = 8'hde;
      read_bytes_nonzero_index[3] = 8'hef;
      read_bytes_nonzero_index[4] = 8'hbe;

      read_shorts[0] = 16'hdead;
      read_shorts[1] = 16'hbeef;
      read_shorts[2] = 16'hcafe;
      read_shorts[3] = 16'hf00d;

      read_words[0] = 32'hdeadbeef;
      read_words[1] = 32'hcafef00d;
      read_words[2] = 32'h00010203;
      read_words[3] = 32'h04050607;

      read_integers[0] = 32'hdeadbeef;
      read_integers[1] = 32'hcafef00d;
      read_integers[2] = 32'h00010203;
      read_integers[3] = 32'h04050607;

      read_longs[0] = 64'hdeadbeefcafef00d;
      read_longs[1] = 64'h0001020304050607;
      read_longs[2] = 64'h08090a0b0c0d0e0f;
      read_longs[3] = 64'h1011121314151617;

      read_customs[0] = 69'hFAdeadbeefcafef00d; //0x001F'FFFF'FFFF'FFFF'FFFF
      read_customs[1] = 69'hF50001020304050607;
      read_customs[2] = 69'h0A08090a0b0c0d0e0f;
      read_customs[3] = 69'h051011121314151617;

      read_customs_nonzero_index_rl[4] = 69'hFAdeadbeefcafef00d; //0x001F'FFFF'FFFF'FFFF'FFFF
      read_customs_nonzero_index_rl[3] = 69'hF50001020304050607;
      read_customs_nonzero_index_rl[2] = 69'h0A08090a0b0c0d0e0f;
      read_customs_nonzero_index_rl[1] = 69'h051011121314151617;

      status = $c32("mon_check()");

      if (status != 0) begin
         $write("%%Error: t_vpi_get_value_array.cpp:%0d: C Test failed\n", status);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
