// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

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
