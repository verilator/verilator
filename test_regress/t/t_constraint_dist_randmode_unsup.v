// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Inner;
  rand int x;
endclass

class COwner;
  rand Inner m[2];
  rand int idx;
  function Inner get(int i);
    return m[i];
  endfunction
  constraint c {
    get(idx).x dist {
      5 := 9,
      10 := 1
    };
  }
  function new();
    m[0] = new;
    m[1] = new;
  endfunction
endclass

class QSum;
  rand int iq[$];
  constraint c {
    iq.sum() dist {
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
    automatic COwner co = new;
    automatic QSum qs = new;
    automatic int ok;
    co.idx.rand_mode(0);
    qs.iq.rand_mode(0);
    ok = co.randomize();
    ok = qs.randomize();
    $finish;
  end
endmodule
