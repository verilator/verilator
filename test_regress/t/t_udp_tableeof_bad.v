// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2009 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

primitive udp_x (a_bad, b, c_bad);
   tri  a_bad;
   output b;
   output c_bad;
   table
      //a   b
      0  :   1;
      1  :   0;
