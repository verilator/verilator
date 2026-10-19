// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
module t (
    inout wire out_and,
    inout wire out_or,
    inout wire id_5, id_9, id_11, id_12, id_16, id_19, id_20, id_21,
    inout wire id_26, id_27, id_32, id_33, id_39, id_40,
    input wire id_14, id_15, id_23, id_24, id_29, id_30, id_34, id_35, id_36
);

  or primOrs (
    out_or, id_5, id_9, id_11, id_12, id_14, id_15, id_16,
    id_19, id_20, id_21, id_23, id_24, id_26, id_27,
    id_29, id_30, id_32, id_33, id_34, id_35, id_36, id_39, id_40);

  and primAnds (
    out_and, id_5, id_9, id_11, id_12, id_14, id_15, id_16,
    id_19, id_20, id_21, id_23, id_24, id_26, id_27,
    id_29, id_30, id_32, id_33, id_34, id_35, id_36, id_39, id_40);

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
