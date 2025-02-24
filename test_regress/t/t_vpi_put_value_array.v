// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Diego Roux. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VERILATOR_COMMENTS
 `define PUBLIC_FLAT_RD /*verilator public_flat_rd*/
 `define PUBLIC_FLAT_RW /*verilator public_flat_rw*/
`else
 `define PUBLIC_FLAT_RD
 `define PUBLIC_FLAT_RW
`endif

module test ();

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   reg [7:0] write_bytes [0:3] `PUBLIC_FLAT_RW;
   reg [7:0] write_bytes_rl [3:0] `PUBLIC_FLAT_RW;
   reg [7:0] write_bytes_nonzero_index [1:4] `PUBLIC_FLAT_RW;

   reg [15:0] write_shorts [0:3] `PUBLIC_FLAT_RW;
   reg [31:0] write_words [0:3] `PUBLIC_FLAT_RW;
   reg [63:0] write_longs [0:3] `PUBLIC_FLAT_RW;
   reg [68:0] write_customs [0:3] `PUBLIC_FLAT_RW;
   reg [68:0] write_customs_nonzero_index_rl [4:1] `PUBLIC_FLAT_RW;

   integer write_integers [0:3] `PUBLIC_FLAT_RW;

   reg [7:0] write_scalar `PUBLIC_FLAT_RW;
   reg [7:0] write_bounds [1:3] `PUBLIC_FLAT_RW;
   reg [7:0] write_inaccessible [0:3] `PUBLIC_FLAT_RD;

`ifdef IVERILOG
   // stop icarus optimizing signals away
   wire redundant = write_bytes[0][0] |
   write_bytes[0][0] |
   write_bytes_rl[0][0] |
   write_bytes_nonzero_index[1][0] |
   write_shorts[0][0] |
   write_words[0][0] |
   write_longs[0][0] |
   write_customs[0][0] |
   write_customs_nonzero_index_rl[1][0] |
   write_integers[0][0] |
   write_scalar[0] |
   write_bounds[1][0] |
   write_inaccessible[0][0];
`endif
   integer status;

   initial begin
`ifdef IVERILOG
     status = $mon_check;
`endif

`ifdef VERILATOR
   status = $c32("mon_check()");
`endif

      if (status != 0) begin
         $write("%%Error: t_vpi_put_value_array.cpp:%0d: C Test failed\n", status);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
