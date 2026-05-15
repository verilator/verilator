// DESCRIPTION: Verilator: Verilog Test module
//
// The code describes a very simple hierarchy of modules.
// The lowest level instantiates avst_interface with name my_avst_if.
// The highest level also instantiates the same interface type
// with the exact same name. The file should lint with no errors
// or warnings other than those disabled by lint_off.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off DECLFILENAME */
/* verilator lint_off UNUSEDSIGNAL */
interface avst_interface;
  logic ready;
  logic valid;

  modport sink_mp (output ready, input  valid);
endinterface

module child (
  output logic ready_out
);
  avst_interface my_avst_if();

  assign ready_out = my_avst_if.ready;
  assign my_avst_if.ready = 1'b1; // drives child.my_avst_if.ready only
endmodule

module wrapper (
  avst_interface.sink_mp my_avst_if
);
  child child_inst (
    .ready_out (my_avst_if.ready) // sole driver of outer my_avst_if.ready
  );
endmodule

module top (
  input  logic in_valid,
  output logic out_ready
);
  avst_interface my_avst_if();

  assign my_avst_if.valid = in_valid;
  assign out_ready = my_avst_if.ready;

  wrapper wrapper_inst (.my_avst_if (my_avst_if));
endmodule
