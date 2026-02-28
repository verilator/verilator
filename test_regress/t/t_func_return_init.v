// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`ifdef verilator
 `define no_optimize(v) $c(v)
`else
 `define no_optimize(v) (v)
`endif
// verilog_format: on

module t;

  class Cls;
    function string unpack_string(int n);
      for (int i = 0; i < n; ++i) begin
        unpack_string = {unpack_string, "."};
        unpack_string[i] = "x";
      end
    endfunction
  endclass

  function static string unpack_static(int n);
    for (int i = 0; i < n; ++i) begin
      unpack_static = {unpack_static, "."};
      unpack_static[i] = "x";
    end
  endfunction

  initial begin
    Cls c;
    string str1[];
    string str2[];
    string s;

    c = new;
    str1 = new[2];
    foreach (str1[i]) str1[i] = c.unpack_string(`no_optimize(3 + i));
    `checks(str1[0], "xxx");
    `checks(str1[1], "xxxx");

    str2 = new[2];
    foreach (str2[i]) str2[i] = unpack_static(`no_optimize(3 + i));
    `checks(str2[0], "xxx");
    `checks(str2[1], "xxxx...");

    $finish;
  end
endmodule
