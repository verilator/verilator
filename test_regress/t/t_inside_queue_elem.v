// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  function string validate_time_precision(string precision);
    static string valid_precision[$] = '{"ps", "ns", "us", "ms", "s"};
    if (!(precision inside {valid_precision})) begin
      return "none";
    end
    return precision;
  endfunction

  initial begin
    automatic int q[$] = {1, 2};
    string s;

    if (!(1 inside {q[0], q[1]})) $stop;
    if (3 inside {q[0], q[1]}) $stop;

    s = validate_time_precision("ps");
    `checks(s, "ps");
    s = validate_time_precision("ns");
    `checks(s, "ns");
    s = validate_time_precision("us");
    `checks(s, "us");
    s = validate_time_precision("ms");
    `checks(s, "ms");
    s = validate_time_precision("s");
    `checks(s, "s");
    s = validate_time_precision("random");
    `checks(s, "none");
    s = validate_time_precision("");
    `checks(s, "none");

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
