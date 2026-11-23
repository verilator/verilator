// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`ifdef NO_COVERAGE
`define EXPECTED `SV_COV_NOCOV
`define EXPECTED_ERROR `SV_COV_NOCOV
`else
`define EXPECTED `SV_COV_OK
`define EXPECTED_ERROR `SV_COV_ERROR
`endif

package pkg;
  function automatic int reset_from_package();
    return $coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_HIER, $root);
  endfunction
endpackage

class Cls;
  // Arguments may be parameters
  localparam int RESET = `SV_COV_RESET;
  function int reset_from_method();
    return $coverage_control(RESET, `SV_COV_ALL, `SV_COV_HIER, $root);
  endfunction
  static function int reset_from_static();
    return $coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_HIER, $root);
  endfunction
endclass

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  int cyc = 0;
  int status;
  logic toggler = 0;
  Cls c = new;
  int control = `SV_COV_RESET;

  initial begin
    // Unsupported arguments return an error when called
    if ($coverage_control(`SV_COV_STOP, `SV_COV_ALL, `SV_COV_HIER, $root) != `EXPECTED_ERROR) `stop;
    if ($coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_HIER, $root) != `EXPECTED_ERROR)
      `stop;
    if ($coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_MODULE, $root) != `EXPECTED_ERROR)
      `stop;
    if ($coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_HIER, t) != `EXPECTED_ERROR) `stop;
    if ($coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_HIER, $root.t) != `EXPECTED_ERROR)
      `stop;
    if ($coverage_control(control + 1, `SV_COV_ALL, `SV_COV_HIER, $root) != `EXPECTED_ERROR)
      `stop;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    toggler <= cyc[0];
    // Counts before the last reset are dropped
    if (cyc == 1) status = pkg::reset_from_package();
    if (cyc == 2) status = c.reset_from_method();
    if (cyc == 3) $coverage_control(control, `SV_COV_ALL, `SV_COV_HIER, $root);
    if (cyc == 4) status = Cls::reset_from_static();
    if (cyc == 5) status = $coverage_control(`SV_COV_RESET, `SV_COV_ALL, `SV_COV_HIER, $root);
    if (cyc >= 1 && cyc <= 5 && cyc != 3 && status != `EXPECTED) `stop;
    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
