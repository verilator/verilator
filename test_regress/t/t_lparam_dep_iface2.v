// DESCRIPTION: Verilator: Get agregate type parameter from array of interfaces
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package p1;
  typedef struct packed {
    int unsigned ABits;
    int unsigned BBits;
  } cfg_t;
endpackage

package p2;
  typedef struct packed {
    int unsigned CBits;
    int unsigned DBits;
  } cfg_t;
endpackage

interface types_if #(parameter p1::cfg_t cfg=0)();
  localparam int ABits = cfg.ABits;
  localparam int BBits = cfg.BBits;

  typedef struct packed {
    logic [cfg.ABits-1:0] a;
    logic [cfg.BBits-1:0] b;
  } a_t;
endinterface

interface io_if #(parameter p1::cfg_t cfg=0)();

  localparam int ABits = cfg.ABits;
  localparam int BBits = cfg.BBits;

  types_if #(cfg) types ();
  typedef types.a_t a_t;
endinterface

module modA(
  io_if io
);

  localparam int ABits = io.types.ABits;
  localparam int BBits = io.types.BBits;

  typedef io.types.a_t a_t;

  initial begin
    #1;
    `checkd(ABits, 8);
    `checkd(BBits, 24);
    `checkd($bits(a_t), 32);
  end

endmodule

module t ();
  localparam p2::cfg_t mcfg = '{
    CBits : 8
    ,DBits : 16
  };

  localparam p1::cfg_t cfg = '{
    ABits : mcfg.CBits
    ,BBits : mcfg.CBits + mcfg.DBits
  };

  io_if #(cfg) modA_io ();

  typedef modA_io.types.a_t a_t;

  modA modA_inst (
    .io(modA_io)
  );

  initial begin
    #2;
    `checkd($bits(a_t), 32);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
