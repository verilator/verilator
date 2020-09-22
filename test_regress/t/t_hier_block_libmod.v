// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA

module t;
   t_flag_relinc_sub i_t_flag_relinc_sub();
endmodule

`ifdef VERILATOR
`verilator_config
hier_block -module "t_flag_relinc_sub"
`verilog
`endif
