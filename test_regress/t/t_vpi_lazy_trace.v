// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Reconstruction + alias + register; verify --vpi-lazy + --trace.
`ifdef T_VPI_LAZY_TRACE
import "DPI-C" function int vpi_lazy_trace_check();
`elsif T_VPI_LAZY_PROTECTIDS
import "DPI-C" function int vpi_lazy_protectids_check();
`endif

module t (
  output logic [6:0] obs
);

`ifdef T_VPI_LAZY_TRACE
`systemc_header
extern "C" int vpi_lazy_trace_check();
`verilog
`elsif T_VPI_LAZY_PROTECTIDS
`systemc_header
extern "C" int vpi_lazy_protectids_check();
`verilog
`endif

  logic [6:0] keep;

  // Reconstructed cmb; alias1 aliases keep.
  logic [6:0] cmb;
  assign cmb = keep + 7'h1;

  logic [6:0] alias1;
  assign alias1 = keep;

  // A reconstructed net: its shadow is a module temp, so the row's net-ness is carried over
  wire [6:0] cmb_net;
  assign cmb_net = cmb ^ 7'h55;

  // An alias of a reconstructed canonical shares its descriptor, so the netlist dump has a
  // vpi-lazy-alias entry
  wire [6:0] cmb_ali;
  assign cmb_ali = cmb;

  assign obs = keep ^ alias1 ^ cmb_net ^ cmb_ali;

initial begin
    keep = 7'h2d;
    #0;
`ifdef T_VPI_LAZY_TRACE
    if ($c32("vpi_lazy_trace_check()")) $fatal(1, "VPI lazy trace check failed");
`elsif T_VPI_LAZY_PROTECTIDS
    if ($c32("vpi_lazy_protectids_check()")) $fatal(1, "VPI lazy protect-ids check failed");
`else
    if ($vpi_lazy_trace_check()) $fatal(1, "VPI lazy trace check failed");
`endif
    $finish;
  end

endmodule
