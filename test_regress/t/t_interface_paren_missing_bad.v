// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Goekce Aydos
// SPDX-License-Identifier: CC0-1.0

// Interface instantiation without parenthesis

interface intf_no_instance;
endinterface

interface intf #(
  parameter int par
);
  logic in;
  modport A(input in);
endinterface

module b (
  intf intf_b_port,
  intf.A intf_b_port_mod
);
  intf intf_b_not_port;
  intf.A intf_b_not_port_mod;
  intf_no_instance intf_no_instance_b_not_port;
endmodule

module d (intf_d_port, intf_d_port_mod);
  intf intf_d_port;
  intf intf_d_not_port;
  intf.A intf_d_port_mod;
  intf.A intf_d_not_port_mod;
  intf_no_instance intf_no_instance_d_not_port;
endmodule

module t;
  intf intf_t_not_port;
  intf.A intf_t_not_port_mod;
  intf_no_instance intf_no_instance_t_not_port;
  intf #(.par(8)) intf_exists();
  b b1 (
    .intf_b_port(intf_exists),
    .intf_b_port_mod(intf_exists.A),
    .intf_b_not_port(intf_exists.A)
  );
  b b2 (
    .intf_b_port(intf_exists),
    .intf_b_port_mod(intf_exists.A)
  );
  d d1 (
    .intf_d_port(intf_exists),
    .intf_d_port_mod(intf_exists.A),
    .intf_d_not_port(intf_exists.A)
  );
  d d2 (
    .intf_d_port(intf_exists),
    .intf_d_port_mod(intf_exists.A)
  );
  initial $finish;
endmodule
