// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  initial begin
    $sdf_annotate("file.sdf");
    $sdf_annotate("file.sdf",);
    $sdf_annotate("file.sdf", t);
    // TArguments are all optional, so test more exhaustively
    $sdf_annotate("file.sdf", t, "config_file", "log_file", "mtm_spec", "scale_factors",
                  "scale_type");
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
