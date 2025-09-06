// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  real r;
  int i;
  initial begin

    // control_constant = `SV_COV_START, `SV_COV_STOP, `SV_COV_RESET, `SV_COV_CHECK
    // coverage_type = `SV_COV_ASSERTION, `SV_COV_FSM_STATE, `SV_COV_STATEMENT,`SV_COV_TOGGLE
    // scope_def = [`SV_COV_MODULE, "unique module def name"], [`SV_COV_HIER, "module name"],
    //               [`SV_COV_MODULE, instance_name], [`SV_COV_HIER, instance_name]
    i = $coverage_control(`SV_COV_START, `SV_COV_TOGGLE, `SV_COV_MODULE, t);
    // returns `SV_COV_OK, `SV_COV_ERROR, `SV_COV_NOCOV, `SV_COV_PARTIAL

    i = $coverage_get(`SV_COV_TOGGLE, `SV_COV_MODULE, t);
    // returns number or `SC_COV_OVERFLOW, `SC_COV_ERROR, `SV_COV_NOCOV

    i = $coverage_get_max(`SV_COV_TOGGLE, `SV_COV_MODULE, t);
    // returns number or `SC_COV_OVERFLOW, `SC_COV_ERROR, `SV_COV_NOCOV

    r = $get_coverage();

    $set_coverage_db_name("filename");

    i = $coverage_save(coverage_type, "filename");
    // returns `SV_COV_OK, `SC_COV_NOCOV, `SC_COV_ERROR

    $load_coverage_db("filename");

    i = $coverage_merge(coverage_type, "filename");
    // returns `SV_COV_OK, `SC_COV_NOCOV, `SC_COV_ERROR

    $finish;
  end

endmodule
