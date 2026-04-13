// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// AstPow (unsigned**unsigned): 2**n -> 1<<n directly
class UnsignedPow2;
  rand bit [3:0] n;
  rand bit [15:0] result;
  constraint c { n inside {[0:7]}; result == 16'(2**n); }
  function void check();
    if (result !== (16'h1 << n)) begin
      $display("FAIL UnsignedPow2: result=%0d expected 2**%0d=%0d", result, n, 16'h1 << n);
      $stop;
    end
  endfunction
endclass

// AstPowUS (unsigned**signed): 2**n -> n>=0 ? 1<<n : 0
class SignedExpPow2;
  rand int signed n;
  rand bit [15:0] result;
  constraint c { n inside {[-2:7]}; result == 16'(2**n); }
  function void check();
    bit [15:0] expected;
    expected = (n >= 0) ? (16'h1 << n) : 16'h0;
    if (result !== expected) begin
      $display("FAIL SignedExpPow2: n=%0d result=%0d expected=%0d", n, result, expected);
      $stop;
    end
  endfunction
endclass

module t;
  UnsignedPow2 u;
  SignedExpPow2 s;

  initial begin
    u = new;
    repeat (20) begin
      if (u.randomize() == 0) begin
        $display("FAIL: UnsignedPow2.randomize() returned 0");
        $stop;
      end
      u.check();
    end

    s = new;
    repeat (30) begin
      if (s.randomize() == 0) begin
        $display("FAIL: SignedExpPow2.randomize() returned 0");
        $stop;
      end
      s.check();
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
