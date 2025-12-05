// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================
module t ();

`ifdef IVERILOG
`elsif USE_VPI_NOT_DPI
`ifdef VERILATOR
`systemc_header
  extern "C" int forceValue();
`verilog
`endif
`else
  import "DPI-C" context function int forceValue();
`endif

  wire nonForceableSignal  /*verilator public_flat_rw*/ = 1'b0;
  integer vpiStatus = 1;

  initial begin

`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("forceValue()");
`else
    vpiStatus = forceValue();
`endif
`elsif IVERILOG
    vpiStatus = $forceValue;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $forceValue;
`else
    vpiStatus = forceValue();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_forceable_bad.cpp:%0d:", vpiStatus);
      $display("C Test failed (could not force value)");
      $stop;
    end
    vpiStatus = 1;  // Reset status to ensure that a function *not* getting
                    // called also causes failure

    $display("*-* All Finished *-*");
    $finish;
  end

endmodule
