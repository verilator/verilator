// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input a,
    output logic b,
    output logic c,
    output logic d,
    output logic e,
    output logic f
);
  class Cls;
    function void set(logic v);
      b <= v;
    endfunction
    function void setViaCall(logic v);
      set(v);
      b <= v;
    endfunction
    virtual function void setVirtual(logic v);
    endfunction
    function void cycleA(logic v, int n);
      if (n > 0) cycleB(v, n - 1);
      set(v);
    endfunction
    function void cycleB(logic v, int n);
      if (n > 0) cycleA(v, n - 1);
    endfunction
    static function int depth(int n);
      return n > 0 ? depth(n - 1) : 0;
    endfunction
    event ev;
    function void trigger();
      ->ev;
      ->>ev;
    endfunction
    function logic get(logic v);
      e <= v;
      return v;
    endfunction
    function void setFromGet(logic v);
      set(get(v));
    endfunction
    event evs[2];
    static function int idx(logic v);
      f <= v;
      return 0;
    endfunction
    function void triggerIndexed(logic v);
      ->evs[idx(v)];
    endfunction
  endclass
  class Derived extends Cls;
    virtual function void setVirtual(logic v);
      d <= v;
    endfunction
  endclass
  Cls obj = new;
  always_comb obj.set(a);
  always_comb obj.setViaCall(a);
  always_comb obj.setVirtual(a);
  always_comb obj.cycleA(a, 1);
  always_comb obj.cycleB(a, 1);
  always_comb obj.trigger();
  assign c = obj.get(a);
  always_comb obj.setFromGet(a);
  always_comb obj.triggerIndexed(a);
  // Not reported
  int depthResult;
  always_comb depthResult = obj.depth(1);
  import "DPI-C" function int dpiFunc(int n);
  int dpiResult;
  always_comb dpiResult = dpiFunc(1);
endmodule
