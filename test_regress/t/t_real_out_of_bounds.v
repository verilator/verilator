// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  class Cls;

    function void m_uvm_execute_field_op();
      real sa_real[3];
      string s;
      // 5 doesn't match array size of 3
      for (int i = 0; i < 5; ++i) begin
        s = $sformatf("%g", sa_real[i]);
        `checks(s, "0");
        s = $sformatf("%p", sa_real[i]);
        `checks(s, "0");
      end
    endfunction
  endclass

  initial begin
    Cls c;
    c = new;
    c.m_uvm_execute_field_op();
    $finish;
  end

endmodule
