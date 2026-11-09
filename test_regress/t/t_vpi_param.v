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


module t #(
  parameter int WIDTH /* verilator public_flat_rd */ = 32
  ) (
    input clk
);

  localparam int DEPTH /* verilator public_flat_rd */ = 16;
  localparam longint PARAM_LONG /* verilator public_flat_rd */ = 64'hFEDCBA9876543210;
  localparam string PARAM_STR /* verilator public_flat_rd */ = "'some string value'";

  typedef string str_arr_t[1:2];
  typedef struct packed {
    logic [2:0] a;
    logic [3:0] b;
  } pair_t;
  localparam string PARAM_STR_ARR[1:2] /* verilator public_flat_rd */ = '{"c", "d"};
  localparam str_arr_t PARAM_STR_ARR_TD /* verilator public_flat_rd */ = '{"e", "f"};
  localparam pair_t PARAM_PAIR /* verilator public_flat_rd */ = '{a: 3'h1, b: 4'h2};
  localparam pair_t PARAM_PAIR_ARR[2:1] /* verilator public_flat_rd */ = '{
    '{a: 3'h3, b: 4'h4}, '{a: 3'h5, b: 4'h6}};

  reg [WIDTH-1:0] mem0 [DEPTH:1] /*verilator public_flat_rw @(posedge clk) */;
  integer    i, status;

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
