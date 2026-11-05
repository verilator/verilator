// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Non-blocking event triggers shall not trigger an element of a dynamically sized array, as they
// update the event like a non-blocking assignment (IEEE 1800-2023 6.21, 15.5.1)

class Cls;
  static event s_te;
  static event s_teq[$];
  event te;
  event teq[$];
endclass

module t (
    input clk
);
  int i;

  event te;
  event tea[2];
  event teq[$];
  event ted[];
  event tes[int];
  event tew[*];
  always @(posedge clk) begin
    ->>te;  // OK
    ->>tea[i];  // OK
    ->>teq[i];  // Error
    ->>teq[0];  // Error
    ->>ted[i];  // Error
    ->>tes[i];  // Error
    ->>tew[i];  // Error
  end

  // Also of class members
  Cls c;
  always @(posedge clk) begin
    ->>Cls::s_te;  // OK
    ->>c.te;  // OK
    ->>Cls::s_teq[i];  // Error
    ->>c.teq[i];  // Error
  end
endmodule
