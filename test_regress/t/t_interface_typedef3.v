// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface ifc;
  typedef logic [3:0] choice_t;
  choice_t q;
  localparam int ONE = 1;
  modport mp(input q);
endinterface

module sub (
    interface.mp iface_mp
);
  typedef iface_mp.choice_t tdef_t;
  tdef_t P;
  initial begin
    `checkd($bits(tdef_t), 4);
  end
endmodule

module t;
  ifc u_ifc ();
  sub u_sub (u_ifc.mp);
endmodule
