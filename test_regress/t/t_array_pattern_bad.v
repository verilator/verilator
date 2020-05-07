// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug1364

module t (/*AUTOARG*/
   // Inputs
   clk, res
   );
   input clk;
   input res;

    typedef struct packed {
        logic [3:0] port_num;
    } info_t;

    info_t myinfo;

    always_comb
      myinfo = '{default: '0,
                 valids: '1};

endmodule
