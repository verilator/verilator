// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class NonAsbstract;
    pure constraint raintBad;  // Bad: Not in abstract class
endclass

module t;
endmodule
