// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

class ConstructorEvent;
  bit value;
  int samples;
  ConstructorEvent self;

  covergroup inner_cg;
    cp: coverpoint value {
      bins one = {1};
    }
  endgroup

  function bit sample_inner();
    ++samples;
    inner_cg.sample();
    return value;
  endfunction

  covergroup watch_cg @(inner_cg);
    cp: coverpoint self.sample_inner() {
      bins one = {1};
    }
  endgroup

  function new();
    value = 1;
    self = this;
    watch_cg = new;
    // IEEE 1800-2023 9.4.2 and 19.3: this handle change immediately samples watch_cg.
    inner_cg = new;
  endfunction
endclass

module t;
  ConstructorEvent mon;

  initial begin
    mon = new;
    `checkd(mon.samples, 1);
    `checkd(int'(mon.inner_cg.get_inst_coverage()), 100);
    `checkd(int'(mon.watch_cg.get_inst_coverage()), 100);
    mon.self = null;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
