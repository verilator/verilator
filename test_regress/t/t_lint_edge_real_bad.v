// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
  // Inputs
  rbad, rok
  );
  input real rbad;
  input real rok;
  event ebad;
  struct packed { int a; } sok;
  logic abad[2];
  logic dbad[];
  logic qbad[$];
  logic aabad[int];
  struct { logic a; } sbad;

  always @ (rok) $stop;
  always @ (sok) $stop;

  always @ (posedge rbad) $stop;
  always @ (posedge ebad) $stop;
  always @ (posedge abad) $stop;
  always @ (posedge dbad) $stop;
  always @ (posedge qbad) $stop;
  always @ (posedge aabad) $stop;
  always @ (posedge sbad) $stop;

endmodule
