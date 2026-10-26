// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Only classes, no module, with parameterized classes used by a non-parameterized class

virtual class Cls #(
    parameter DECODE_W
);
endclass

class ClsDefault #(
    int P = 1
);
endclass

class ClsUser;
  Cls #(8) m_cls;
  ClsDefault m_default;
  ClsDefault #(2) m_two;
endclass
