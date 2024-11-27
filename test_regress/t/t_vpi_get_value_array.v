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
   reg [15:0] read_shorts [0:3] `PUBLIC_FLAT_RD;
   reg [31:0] read_words [0:3] `PUBLIC_FLAT_RD;
   reg [31:0] read_words_rl [3:0] `PUBLIC_FLAT_RD;
   reg [63:0] read_longs [0:3] `PUBLIC_FLAT_RD;
   reg [127:0] read_quads [0:3] `PUBLIC_FLAT_RD;
   integer read_integers [0:3] `PUBLIC_FLAT_RD;
   reg [7:0] read_scalar `PUBLIC_FLAT_RD;
   reg [7:0] read_bounds [1:3] `PUBLIC_FLAT_RD;

   integer status;

   initial begin
      read_bytes[0] = 8'hde;
      read_bytes[1] = 8'had;
      read_bytes[2] = 8'hbe;
      read_bytes[3] = 8'hef;

      read_shorts[0] = 16'hdead;
      read_shorts[1] = 16'hbeef;
      read_shorts[2] = 16'hcafe;
      read_shorts[3] = 16'hf00d;

      read_words[0] = 32'hcafef00d;
      read_words[1] = 32'hdeadbeef;
      read_words[2] = 32'h01234567;
      read_words[3] = 32'h89abcdef;

      read_words_rl[0] = 32'hdeadbeef;
      read_words_rl[1] = 32'hcafef00d;
      read_words_rl[2] = 32'h01234567;
      read_words_rl[3] = 32'h89abcdef;

      read_longs[0] = 64'hdeadbeefcafef00d;
      read_longs[1] = 64'h0123456789abcdef;
      read_longs[2] = 64'hbeefdeadf00dcafe;
      read_longs[3] = 64'h45670123cdef89ab;

      read_quads[0] = 128'hdeadbeefcafef00d0123456789abcdef; // 0 -> 15
      read_quads[1] = 128'hbeefdeadf00dcafe45670123cdef89ab; // 16 -> 31
      read_quads[2] = 128'hefbeadde0df0feca67452301efcdab89; // 32 -> 47
      read_quads[3] = 128'hfeebdaedd00fefac32107654ba98fedc; // 48 -> 63

      read_integers[0] = -2147483648;
      read_integers[1] = 2147483647;
      read_integers[2] = 0;
      read_integers[3] = 1234567890;

      status = $c32("mon_check()");

      if (status != 0) begin
         $write("%%Error: t_vpi_get.cpp:%0d: C Test failed\n", status);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
