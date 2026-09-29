// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t (
    output logic [6:0] obs
);

  logic [6:0] keep;

  logic [6:0] cmb;
  assign cmb = keep + 7'h1;

  logic [6:0] alias1;
  assign alias1 = keep;

  wire [6:0] cmb_net;
  assign cmb_net = cmb ^ 7'h55;

  wire [6:0] cmb_ali;
  assign cmb_ali = cmb;

  assign obs = keep ^ alias1 ^ cmb_net ^ cmb_ali;

`ifndef NO_T_VPI_DUMP
  import "DPI-C" context function void t_vpi_dump_values();
  initial t_vpi_dump_values();
`endif

  initial begin
    keep = 7'h2d;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
