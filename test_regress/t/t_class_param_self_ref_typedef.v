// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 8.25.1: inside a parameterized class, a bare class name used
// without #() denotes the current specialization. So in the function below the
// return type spelled `holder::my_item_t` and the unqualified local `my_item_t`
// must denote the same type. Previously the class-qualified reference stayed
// bound to the default instance, so the two widened to different
// specializations and the return failed type checking.

package pkg;
  class item_base #(type DATA = int);
    DATA value;
  endclass

  class holder #(type FIN = int);
    typedef item_base#(FIN) my_item_t;

    virtual function holder::my_item_t get_bare();
      my_item_t item;
      return item;
    endfunction
  endclass
endpackage

module t;
  import pkg::*;

  // Non-default parameter, so the specialization differs from the template
  // default and the bug is observable.
  holder#(byte) h;

  initial begin
    automatic holder#(byte)::my_item_t got;
    h = new;
    got = h.get_bare();
    if ($bits(got.value) != 8) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
