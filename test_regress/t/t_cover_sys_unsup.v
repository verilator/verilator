// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  real r;
  int i;
  initial begin

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
