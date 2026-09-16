// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilog_format: off
module t;
  string s;

  initial begin
    $display("""First "quoted"\nsecond\
third
fourth""");

    // IEEE 1800-2023 5.9: a backslash immediately before a newline in a
    // triple-quoted string is ignored, as in a quoted string
    s = """one \
two""";
    `checks(s, "one two");

    s = """a\
b\
c""";
    `checks(s, "abc");

    s = """one
two""";
    `checks(s, "one\ntwo");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
// verilog_format: on
