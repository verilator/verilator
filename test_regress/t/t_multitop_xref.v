// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off MULTITOP

module dut;

  bit [15:0] acp;

  function void reset();
    acp = 0;
  endfunction

  initial reset();

endmodule

module t;
  class Cls;
    static task rw();
      dut.acp++;
    endtask
  endclass

  initial begin
    Cls c;
    c = new;
    c.rw();
    `checkd(dut.acp, 1);
    $finish;
  end

endmodule
