// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Deanyone Su
// SPDX-License-Identifier: CC0-1.0

// Many instances of one interface, each with modports and some logic
// (performance test for modport resolution after scoping)

interface ctrl_if;
  logic [31:0] data;
  logic valid;
  logic ready;
  logic [31:0] data_q;
  always_comb ready = !valid || data[0];
  assign data_q = data ^ 32'h5a5a5a5a;
  modport master_mp(output data, output valid, input ready);
  modport slave_mp(input data, input valid, output ready);
endinterface

module sink (
    ctrl_if.slave_mp s,
    output logic o
);
  assign o = s.valid & s.data[3];
endmodule

module t #(
    parameter int N = 4000
) (
    input logic [31:0] in,
    output logic [N-1:0] out
);
  ctrl_if intfs[N] ();
  for (genvar i = 0; i < N; i++) begin : g
    assign intfs[i].data = in + i;
    assign intfs[i].valid = in[i%32];
    sink u_sink (
        .s(intfs[i]),
        .o(out[i])
    );
  end
endmodule
