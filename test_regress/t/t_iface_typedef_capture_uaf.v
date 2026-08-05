// DESCRIPTION: Verilator: Test interface typedef capture after parameter cloning
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilator lint_off DECLFILENAME

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0)
// verilog_format: on

interface avmm_if #(
    parameter int DW = 32
);
  typedef struct packed {
    logic [DW-1:0] writedata;
    logic write;
  } request_t;

  request_t req;

  modport master(output req);
  modport slave(input req);
endinterface

module avmm_autopipeline (
    avmm_if.slave master,
    avmm_if.master slave
);
  typedef master.request_t request_t;
  request_t internal_req;

  assign internal_req = master.req;
  always_comb slave.req = internal_req;
endmodule

module t;
  for (genvar g = 0; g < 2; ++g) begin : gen_block
    avmm_if #(.DW(32 * (g + 1))) m_if ();
    avmm_if #(.DW(32 * (g + 1))) s_if ();
    avmm_autopipeline pipe (.master(m_if), .slave(s_if));
  end

  initial begin
    #1;
    `checkd($bits(gen_block[0].pipe.internal_req), 33);
    `checkd($bits(gen_block[1].pipe.internal_req), 65);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
