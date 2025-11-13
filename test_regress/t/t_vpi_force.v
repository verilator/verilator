// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================
`define STRINGIFY(x) `"x`"

module t ();

`ifdef IVERILOG
`elsif USE_VPI_NOT_DPI
`ifdef VERILATOR
`systemc_header
  extern "C" int baselineValue();
  extern "C" int forceValues();
  extern "C" int releaseValues();
  extern "C" int checkValuesForced();
  extern "C" int checkValuesReleased();
`verilog
`endif
`else
  import "DPI-C" context function int baselineValue();
  import "DPI-C" context function int forceValues();
  import "DPI-C" context function int releaseValues();
  import "DPI-C" context function int checkValuesForced();
  import "DPI-C" context function int checkValuesReleased();
`endif

  reg clk;

  initial begin
    clk = 0;
    forever #1 clk = ~clk;
  end

  Test test (.clk(clk));

  integer vpiStatus = 1;

  initial begin
`ifdef WAVES
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
`endif

    #3;  // Wait a bit before triggering the force to see a change in the traces

`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("forceValues()");
`else
    vpiStatus = forceValues();
`endif
`elsif IVERILOG
    vpiStatus = $forceValues;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $forceValues;
`else
    vpiStatus = forceValues();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (could not force value)");
      $stop;
    end
    vpiStatus = 1;  // Reset status to ensure that a function *not* getting
                    // called also causes failure

    #4;  // Time delay to ensure setting and checking values does not happen
         // at the same time, so that the signals can have their values overwritten
         // by other processes

`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkValuesForced()");
`else
    vpiStatus = checkValuesForced();
`endif
`elsif IVERILOG
    vpiStatus = $checkValuesForced;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkValuesForced;
`else
    vpiStatus = checkValuesForced();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value after forcing does not match expectation)");
      $stop;
    end
    vpiStatus = 1;

    #3;


`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("releaseValues()");
`else
    vpiStatus = releaseValues();
`endif
`elsif IVERILOG
    vpiStatus = $releaseValues;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $releaseValues;
`else
    vpiStatus = releaseValues();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (could not release value)");
      $stop;
    end
    vpiStatus = 1;

    #4;

`ifdef VERILATOR
`ifdef USE_VPI_NOT_DPI
    vpiStatus = $c32("checkValuesReleased()");
`else
    vpiStatus = checkValuesReleased();
`endif
`elsif IVERILOG
    vpiStatus = $checkValuesReleased;
`elsif USE_VPI_NOT_DPI
    vpiStatus = $checkValuesReleased;
`else
    vpiStatus = checkValuesReleased();
`endif

    if (vpiStatus != 0) begin
      $write("%%Error: t_vpi_force.cpp:%0d:", vpiStatus);
      $display("C Test failed (value after releasing does not match expectation)");
      $stop;
    end

    #5 $display("*-* All Finished *-*");
    $finish;
  end

endmodule

module Test (
    input clk
);

  logic clockedReg  /*verilator public_flat_rw*/  /*verilator forceable*/, assignedWire;
`ifdef VERILATOR
  assign assignedWire = $c32("baselineValue()");
`else
  initial begin
    assignedWire = $baselineValue;
  end
`endif
  always @(posedge clk) begin
    clockedReg <= assignedWire;
  end

`ifdef TEST_VERBOSE
  initial begin
    $display("[time]\t\tclk\t\tassignedWire\tclockedReg");
    forever #1 $display("[%0t]\t\t%b\t\t%b\t\t%b", $time, clk, assignedWire, clockedReg);
  end
`endif

endmodule
