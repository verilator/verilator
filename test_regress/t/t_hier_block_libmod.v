// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  t_flag_relinc_sub i_t_flag_relinc_sub();
  lib_sub i_lib_sub();
endmodule

module lib_sub;
  string s;
  initial begin
    s = $sformatf("lib=%l");
    `checks(s, "lib=lib_work.lib_sub");
  end
endmodule

`ifdef VERILATOR
`verilator_config
hier_block -module "t_flag_relinc_sub"
hier_block -module "lib_sub"
`verilog
`endif
