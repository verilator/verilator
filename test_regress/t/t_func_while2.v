// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  int i;
  string value;

  function automatic int count();
    ++i;
    value = {value, $sformatf(" count%0d", i)};
    return i;
  endfunction

  initial begin
    value = "";
    i = 0;
    while (count() <= 2) begin
      // verilator unroll_disable
      value = {value, " loop"};
    end
    `checks(value, " count1 loop count2 loop count3");

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
