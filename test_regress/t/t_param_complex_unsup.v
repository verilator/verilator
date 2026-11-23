// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef union {
  int a;
  int b;
} unpacked_union_t;

module t;
  localparam bit MATCH = eval_case_inside_range_string("c") == 1;
  localparam int ARRAY_UNION_RESULT = evaluate_array_union();

  function automatic int eval_case_inside_range_string(input string value);
    case (value) inside
      ["b" : "d"]: eval_case_inside_range_string = 1;
      default: eval_case_inside_range_string = 2;
    endcase
  endfunction

  function automatic int evaluate_array_union();
    unpacked_union_t values[1];
    values[0].a = 1;
    return 0;
  endfunction
endmodule
