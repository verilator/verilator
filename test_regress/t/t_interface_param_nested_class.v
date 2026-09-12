// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Verilator Authors.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A parameterized class nested in a specialized parameterized interface must
// produce distinct, well-formed class-package names during C++ emission.
interface intf #(int P = 1);
  class Cls #(int Q);
  endclass

  Cls #(P) obj;
endinterface

module t;
  intf #(2) intf_i();

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
