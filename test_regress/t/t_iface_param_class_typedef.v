// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test that parameterized class typedefs work as interface type parameters
// See issue #6983

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class flux_st #(parameter int WIDTH=32);
  typedef struct packed { logic [WIDTH-1:0] data; } pld_t;
endclass

interface flux_if #(parameter type PLD_T = logic);
  logic rdy;
  logic vld;
  PLD_T pld;
  modport drive (input rdy, output vld, output pld);
  modport sink (output rdy, input vld, input pld);
endinterface

module t;
  // Test using parameterized class typedef as interface type parameter
  flux_if #(flux_st#(64)::pld_t) w_flux_st ();

  initial begin
    `checkd($bits(w_flux_st.pld), 64);
    w_flux_st.pld.data = 64'hDEADBEEF_CAFEBABE;
    `checkd(w_flux_st.pld.data, 64'hDEADBEEF_CAFEBABE);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
