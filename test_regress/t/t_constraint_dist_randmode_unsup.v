// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Inner;
  rand int x;
endclass

class QOwner;
  rand Inner q[$];
  constraint c {
    q[0].x dist {
      5 := 9,
      10 := 1
    };
  }
  function new();
    Inner tmp = new;
    q.push_back(tmp);
  endfunction
endclass

class QValue;
  rand int iq[$];
  constraint c {
    iq[0] dist {
      5 := 9,
      10 := 1
    };
  }
  function new();
    iq.push_back(1);
  endfunction
endclass

module t;
  initial begin
    automatic QOwner qo = new;
    automatic QValue qv = new;
    automatic int ok;
    qo.q.rand_mode(0);
    qv.iq.rand_mode(0);
    ok = qo.randomize();
    ok = qv.randomize();
    $finish;
  end
endmodule
