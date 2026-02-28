// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: Unlicense

module t;
   t_flag_relinc_sub i_t_flag_relinc_sub();
endmodule

`ifdef VERILATOR
`verilator_config
hier_block -module "t_flag_relinc_sub"
`verilog
`endif
