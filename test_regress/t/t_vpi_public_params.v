// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Call the C++-linkage wrapper of a test function, as $c cannot declare an extern "C" function
`define CPP_CALL(f) $c32(`"[] { extern int f``_cpp(); return f``_cpp(); }()`")

`ifdef USE_VPI_NOT_DPI
//We call it via $c so we can verify DPI isn't required - see bug572
`else
import "DPI-C" context function int mon_check();
`endif

// Copy of t_vpi_public_params.v but with the inline public taken out
module t #(
    parameter int WIDTH = 32
) (
    input clk
);

  localparam int DEPTH = 16;
  localparam longint PARAM_LONG = 64'hFEDCBA9876543210;
  localparam string PARAM_STR = "'some string value'";

  reg [WIDTH-1:0] mem0[DEPTH:1];
  integer i, status;

  // Test loop
  initial begin
`ifdef VERILATOR
    status = `CPP_CALL(mon_check);
`endif
`ifdef IVERILOG
    status = $mon_check();
`endif
`ifndef USE_VPI_NOT_DPI
    status = mon_check();
`endif

    if (status != 0) begin
      $write("%%Error: t_vpi_param.cpp:%0d: C Test failed\n", status);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule : t
