// DESCRIPTION: Verilator: Interface typedef owner lookup must skip sibling classes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0)
// verilog_format: on

interface types_if;
  // This is a preceding sibling of word_t, not its owner.
  class Unrelated;
  endclass
  typedef bit word_t;
endinterface

module reader(types_if source);
  typedef source.word_t word_t;
  word_t value;
  initial begin
    value = 1;
    `checkd(value, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module t;
  types_if source();
  reader r(source);
endmodule
