// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%s exp=%s\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  string expected_scope = $sformatf("%m.sib");

  initial
  fork : fblk
    begin
      $write("Forked");
    end
    begin
      `checkd(t.visible, 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  join : fblk

  bit visible = 1;

  // Sibling of the named fork: must not inherit fblk's %m scope
  final begin : sib
    `checks($sformatf("%m"), expected_scope);
  end

endmodule
