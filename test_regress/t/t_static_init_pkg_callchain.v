// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nick
// SPDX-License-Identifier: CC0-1.0

package p_cmd;
  class CmdProc;
    static CmdProc m_inst;
    static function CmdProc get_inst();
      if (m_inst == null) m_inst = new;
      return m_inst;
    endfunction
    function void get_arg_values(string prefix, ref string values[$]);
      values.push_back({prefix, "ok"});
    endfunction
  endclass

  const CmdProc cmdline_proc = CmdProc::get_inst();

  class Cfg;
    static string values[$];
    static function void set_cl();
      CmdProc clp = CmdProc::get_inst();
      if (values.size() == 0) void'(cmdline_proc.get_arg_values("+cfg=", values));
      if (clp == null) $stop;
    endfunction
  endclass
endpackage

module t;
  import p_cmd::*;

  function automatic int run_cfg();
    Cfg::set_cl();
    return 1;
  endfunction

  int y = run_cfg();

  initial begin
    if (y != 1) $stop;
    if (Cfg::values.size() != 1) $stop;
    if (Cfg::values[0] != "+cfg=ok") $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
