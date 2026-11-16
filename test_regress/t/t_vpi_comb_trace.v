// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t (
    output logic [6:0] obs
`ifdef T_VPI_FORCE_PORT
    /* verilator forceable */
`endif
);

`ifdef T_VPI_FORCE_PORT
  import "DPI-C" context function int forceTopPort(input int value, input bit releasePort);
  import "DPI-C" context function int checkTopPort(input int expected);
`endif

  logic [6:0] keep;

  logic [6:0] cmb;
  assign cmb = keep + 7'h1;

  logic [6:0] alias1;
  assign alias1 = keep;

  wire [6:0] cmb_net;
  assign cmb_net = cmb ^ 7'h55;

  wire [6:0] cmb_ali;
  assign cmb_ali = cmb;

`ifdef T_VPI_FORCE_PORT
  assign obs = keep;
`else
  assign obs = keep ^ alias1 ^ cmb_net ^ cmb_ali;
`endif

`ifndef NO_T_VPI_DUMP
  import "DPI-C" context function void t_vpi_dump_values();
  initial t_vpi_dump_values();
`endif

  initial begin
    keep = 7'h2d;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    #1;
`ifdef T_VPI_FORCE_PORT
    `checkd(checkTopPort(32'h2d), 0);
    `checkd(forceTopPort(32'h23, 0), 0);
    #1;
    `checkd(checkTopPort(32'h23), 0);
    keep = 7'h31;
    `checkd(forceTopPort(32'h4a, 0), 0);
    #1;
    `checkd(checkTopPort(32'h4a), 0);
    `checkd(forceTopPort(0, 1), 0);
    #1;
    `checkd(checkTopPort(32'h31), 0);
`endif
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
