// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test: constraints on class object array element members (fixed-size arrays)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=[%0d:%0d]\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off IMPLICITSTATIC */

class item_t;
  rand bit [7:0] value;
endclass

// Scenario A: foreach with range constraint
class container_a;
  rand item_t items[4];
  constraint val_c {
    foreach (items[i]) {
      items[i].value inside {[10 : 200]};
    }
  }
  function new();
    foreach (items[i]) items[i] = new;
  endfunction
endclass

// Scenario B: foreach with ordering constraint
class container_b;
  rand item_t items[4];
  constraint order_c {
    foreach (items[i]) {
      if (i != 0) {items[i].value > items[i-1].value;}
    }
  }
  function new();
    foreach (items[i]) items[i] = new;
  endfunction
endclass

// Scenario C: constant-index constraint (no foreach)
class container_c;
  rand item_t items[4];
  constraint val_c {
    items[0].value < items[1].value;
    items[1].value < items[2].value;
    items[2].value < items[3].value;
  }
  function new();
    foreach (items[i]) items[i] = new;
  endfunction
endclass

module t;
  initial begin
    automatic container_a ca = new;
    automatic container_b cb = new;
    automatic container_c cc = new;
    automatic int ok;

    repeat (20) begin
      // Scenario A: foreach range
      ok = ca.randomize();
      `checkd(ok, 1);
      for (int i = 0; i < 4; i++) begin
        `check_range(ca.items[i].value, 10, 200);
      end

      // Scenario B: foreach ordering
      ok = cb.randomize();
      `checkd(ok, 1);
      for (int i = 1; i < 4; i++) begin
        if (cb.items[i].value <= cb.items[i-1].value) begin
          $write("%%Error: %s:%0d: ordering violated: items[%0d]=%0d <= items[%0d]=%0d\n",
                 `__FILE__, `__LINE__, i, cb.items[i].value, i - 1, cb.items[i-1].value);
          `stop;
        end
      end

      // Scenario C: constant-index ordering
      ok = cc.randomize();
      `checkd(ok, 1);
      for (int i = 1; i < 4; i++) begin
        if (cc.items[i].value <= cc.items[i-1].value) begin
          $write("%%Error: %s:%0d: ordering violated: items[%0d]=%0d <= items[%0d]=%0d\n",
                 `__FILE__, `__LINE__, i, cc.items[i].value, i - 1, cc.items[i-1].value);
          `stop;
        end
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
