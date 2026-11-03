// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A net driven by an output port plus an initial value or continuous
// assignment; inout connections are bus connections.

module t_pin_sub (output logic [31:0] o);
  assign o = 1;
endmodule

module t_pin_sub_inout (inout logic [31:0] o);
endmodule

module t_pin_sub16 (output logic [15:0] o);
  assign o = 1;
endmodule

module t_pin_sub1 (output logic o);
  assign o = 1;
endmodule

module t_pin_sub_undriven (output logic [31:0] o);
endmodule

module t_pin_sub_part (output logic [31:0] o);
  assign o[3:0] = 1;
endmodule

module t_pin_sub_readonly (output logic [31:0] o);
  always @(o)
    if (o[0]) $display("");
endmodule

module t_lint_multidriven_pin_bad (
  input logic [31:0] a,
  input logic [31:0] b);
  // Initial value plus output port connection  // <--- Warning
  wire [31:0] init_pin = 0;
  // A pure-Z initial value drives no value, so no warning
  wire [31:0] init_z = 32'bz;
  // Continuous assignment plus output port connection  // <--- Warning
  wire [31:0] cont_pin;
  // A pure-Z continuous assignment drives no value, so no warning
  wire [31:0] cont_z;
  // Bit-range continuous assignment plus whole-net port connection
  // <--- Warning
  wire [31:0] cont_sel;
  // Two output port connections  // <--- Warning
  wire [31:0] two_pins;
  // An output port and an inout port share the net, like a bus: no warning
  wire [31:0] inout_bus;
  // Two port connections of disjoint bit ranges, so no warning
  wire [31:0] two_sel;
  // A port the child module never drives only adds Z, so no warning
  wire [31:0] undriven_port;
  // The child drives some bits of the port, so it is a real driver
  // <--- Warning
  wire [31:0] part_port = 0;
  // The child reads its port but never drives it, so no warning
  wire [31:0] readonly_port;
  // One driving and one undriven port plus a continuous assignment
  // <--- Warning
  wire [31:0] mixed_port;
  // Two undriven ports seen first, then a driving port and a continuous
  // assignment: the driving port still counts  // <--- Warning
  wire [31:0] mixed2_port;
  // Tri-family nets resolve multiple drivers by design (strength
  // resolution, the built-in pull of tri0/1 and supply0/1), so a port
  // alongside their default drivers is not a conflict  // <--- silent
  tri [31:0] tri_pin = 0;
  // The supply net's built-in pull plus a port connection is its
  // intended use, so no warning  // <--- silent
  supply0 supply_pin;
  // A Z constant on a conditional data path is the open-drain
  // "drives only sometimes" style, so no warning
  wire [31:0] zcond_pin;
  // Wired nets combine their drivers by design (the interrupt-bus
  // idiom), so two driving ports are not a conflict  // <--- silent
  trior [31:0] wor_bus;
  // A Z constant inside a comparison never reaches the net, so the
  // assign is a real driver  // <--- Warning
  wire zcmp_pin;
  // A logic variable is not a net, so its port connection is not a
  // second driver: no warning
  logic [31:0] logic_pin;
  // Two continuous assignments without a port connection, so no warning
  wire [31:0] no_pin;
  // Suppressed with lint_off on the declaration
  // verilator lint_off MULTIDRIVEN
  wire [31:0] init_off = 0;
  // verilator lint_on MULTIDRIVEN
  assign cont_pin = a;
  assign cont_z = 32'bz;
  assign cont_sel[3:0] = a[3:0];
  assign undriven_port = a;
  assign readonly_port = a;
  assign mixed_port = a;
  assign mixed2_port = a;
  assign no_pin = a;
  assign no_pin = b;
  assign zcond_pin = b[0] ? a : 32'bz;
  assign zcmp_pin = a === 'z;
  assign logic_pin = a;
  t_pin_sub i1 (.o(init_pin));
  t_pin_sub i2 (.o(init_z));
  t_pin_sub i3 (.o(cont_pin));
  t_pin_sub i4 (.o(cont_z));
  t_pin_sub i5 (.o(cont_sel));
  t_pin_sub_undriven i15 (.o(undriven_port));
  t_pin_sub_part i16 (.o(part_port));
  t_pin_sub_readonly i17 (.o(readonly_port));
  t_pin_sub_undriven i18 (.o(mixed_port));
  t_pin_sub i19 (.o(mixed_port));
  t_pin_sub_undriven i26 (.o(mixed2_port));
  t_pin_sub_undriven i27 (.o(mixed2_port));
  t_pin_sub i28 (.o(mixed2_port));
  t_pin_sub i6 (.o(two_pins));
  t_pin_sub i7 (.o(two_pins));
  t_pin_sub i13 (.o(two_pins));
  t_pin_sub i12 (.o(init_off));
  t_pin_sub i20 (.o(tri_pin));
  t_pin_sub1 i21 (.o(supply_pin));
  t_pin_sub i22 (.o(zcond_pin));
  t_pin_sub i29 (.o(wor_bus));
  t_pin_sub i30 (.o(wor_bus));
  t_pin_sub1 i23 (.o(zcmp_pin));
  t_pin_sub i24 (.o(logic_pin));
  generate
    // A net under a generate is a separate net, so the check still
    // applies  // <--- Warning
    wire [31:0] gen_pin = 0;
    t_pin_sub i25 (.o(gen_pin));
  endgenerate
  t_pin_sub i10 (.o(inout_bus));
  t_pin_sub_inout i11 (.o(inout_bus));
  t_pin_sub16 i8 (.o(two_sel[31:16]));
  t_pin_sub16 i9 (.o(two_sel[15:0]));
  initial $display("init_pin=%h init_z=%h cont_pin=%h cont_z=%h cont_sel=%h two_pins=%h inout_bus=%h two_sel=%h no_pin=%h init_off=%h undriven_port=%h part_port=%h readonly_port=%h mixed_port=%h tri_pin=%h supply_pin=%h wor_bus=%h",
                   init_pin, init_z, cont_pin, cont_z, cont_sel, two_pins, inout_bus, two_sel, no_pin, init_off,
                   undriven_port, part_port, readonly_port, mixed_port, tri_pin, supply_pin, wor_bus);
endmodule
