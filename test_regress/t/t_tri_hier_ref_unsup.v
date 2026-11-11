// DESCRIPTION: Verilator: Verilog Test module
//
// Test case #1: Hierarchical write to a non-interface submodule's tri wire.
// A parent module drives a child module's internal tri wire via hierarchical
// reference, in addition to the child's own internal driver.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off MULTIDRIVEN

module sub_with_tri (
    input we_internal
);
  tri [7:0] bus;
  // Internal driver: drives 8'hAA when we_internal is high
  assign bus = we_internal ? 8'hAA : 8'hzz;
endmodule

module sub_inout (
    inout wire io
);
  initial begin
    #1;
    `checkh(io, 1'b1);
  end
endmodule

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

  logic sub_we_internal;
  sub_with_tri u_sub (.we_internal(sub_we_internal));

  logic hier_we;
  // Drive u_sub.bus hierarchically from this module
  assign u_sub.bus = hier_we ? 8'hBB : 8'hzz;

  // Unconnected inout driven hierarchically (issue #5318)
  // verilator lint_off PINMISSING
  sub_inout u_inout ();
  // verilator lint_on PINMISSING
  assign u_inout.io = 1'b1;

  initial begin
    // All drivers off -> high-Z
    #1;
    hier_we = 1'b0;
    sub_we_internal = 1'b0;
    #1;
    `checkh(u_sub.bus, 8'hzz);

    // External hierarchical driver on
    #1;
    hier_we = 1'b1;
    sub_we_internal = 1'b0;
    #1;
    `checkh(u_sub.bus, 8'hBB);

    // Internal driver on, external off
    #1;
    hier_we = 1'b0;
    sub_we_internal = 1'b1;
    #1;
    `checkh(u_sub.bus, 8'hAA);

    // Both off again
    #1;
    hier_we = 1'b0;
    sub_we_internal = 1'b0;
    #1;
    `checkh(u_sub.bus, 8'hzz);

    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
