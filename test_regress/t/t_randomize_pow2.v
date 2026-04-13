// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test 2**n in constraints: ConstraintExprVisitor transforms 2**n -> 1<<n for SMT.
// Only unsigned exponent variants (AstPow, AstPowSU) are supported.
// Signed exponent variants (AstPowSS, AstPowUS) retain the CONSTRAINTIGN warning.

class Pow2Test;
  rand bit [3:0] n;
  rand bit [15:0] result;

  // AstPow (unsigned**unsigned): 2**n -> 1<<n
  constraint c_pow2 {
    n inside {[0:7]};
    result == 16'(2**n);
  }

  function void check();
    if (result !== (16'h1 << n)) begin
      $display("FAIL: result=%0d expected 2**%0d=%0d", result, n, 16'h1 << n);
      $stop;
    end
  endfunction
endclass

module t;
  Pow2Test obj;

  initial begin
    obj = new;
    repeat (20) begin
      if (obj.randomize() == 0) begin
        $display("FAIL: randomize() returned 0");
        $stop;
      end
      obj.check();
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
