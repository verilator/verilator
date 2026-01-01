// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//

package aer;
  typedef struct packed {
    int unsigned NumCca;
  } cfg_t;
endpackage

package cca;
  typedef struct packed {
    int unsigned NumCc;
  } cfg_t;
endpackage

package amb;
  typedef struct packed {
    logic start;
  } rule_t;
endpackage

interface tb_if #(parameter cca::cfg_t cfg=0)();
  typedef logic [$clog2(cfg.NumCc)-1:0] cc_index_t;
endinterface

module modA#(
  parameter aer::cfg_t cfg=0,
  //
  localparam type rule_t = amb::rule_t
)();

  localparam cca::cfg_t cca_cfg = '{
    NumCc : 4
  };

  tb_if #(cca_cfg) tb_io();
  localparam type cc_index_t = tb_io.cc_index_t;
endmodule

module tb();

  localparam aer::cfg_t aer_cfg= '{
    NumCca : 2
  };

  modA #(aer_cfg) modA();

  initial begin
    #1;
    $finish;
  end

endmodule
