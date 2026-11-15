// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module pulled_stream_port (
    output wire [8:0] pad
);
  pullup (pad);
endmodule

module pulled_array_port (
    output tri1 [6:0] pad [1:0]
);
endmodule

module pulled_pair_port (
    output tri1 [1:0] pad
);
endmodule

interface pulled_port_if;
  wire [8:0] pad;
endinterface

module unpulled_port #(
    parameter int WIDTH = 9
) (
    output wire [WIDTH-1:0] pad
);
  assign pad = 'z;
endmodule

module unpulled_array_port (
    inout wire [6:0] pad [1:0]
);
endmodule

module t;
  // Repeated destinations can be folded from a concatenation into a replication.
  wire repeated;
  pulled_pair_port repeated_pull (.pad({repeated, repeated}));

  // Stream truncation still requires support for matching data, enables, and pulls.
  wire [6:0] narrow_left, narrow_right;
  // verilator lint_off WIDTHEXPAND
  pulled_stream_port left_truncate (.pad({<<2{narrow_left}}));
  pulled_stream_port right_truncate (.pad({>>{narrow_right}}));
  // verilator lint_on WIDTHEXPAND

  // Pull propagation does not support hierarchical or unpacked member destinations.
  pulled_port_if pulled_if ();
  pulled_stream_port interface_pull (.pad(pulled_if.pad));
  struct {
    logic [8:0] pad;
  } unpacked_pulled;
  pulled_stream_port member_pull (.pad(unpacked_pulled.pad));

  // Pulled ports must also diagnose unsupported unpacked element connections.
  wire [8:0] pulled_elements [1:0];
  pulled_stream_port element_pull (.pad(pulled_elements[0]));

  // An unpacked array slice reaches pull propagation as a SliceSel.
  wire [6:0] pulled_array [3:0];
  pulled_array_port slice_pull (.pad(pulled_array[2:1]));

  // Without a pull diagnostic, these destinations must still report unsupported LHSs.
  wire unpulled_repeated;
  unpulled_port #(.WIDTH(2)) repeated_no_pull (.pad({unpulled_repeated, unpulled_repeated}));
  struct {
    logic [8:0] pad;
  } unpacked_unpulled;
  unpulled_port member_no_pull (.pad(unpacked_unpulled.pad));
  wire [8:0] unpulled_elements [1:0];
  unpulled_port element_no_pull (.pad(unpulled_elements[0]));
  wire [6:0] unpulled_array [3:0];
  unpulled_array_port slice_no_pull (.pad(unpulled_array[2:1]));
endmodule
