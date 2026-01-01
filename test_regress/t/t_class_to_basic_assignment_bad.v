// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  int phase_done;

  static function Foo get();
    Foo ans = new;
    return ans;
  endfunction

  static function int create();
    return 3;
  endfunction

  function string get_name();
    return "bar";
  endfunction

  function void add(Foo phase);
    Foo new_node;
    if (new_node.get_name() == "run") begin
      new_node.phase_done = get();
    end
    else begin
      new_node.phase_done = create();
    end
  endfunction
endclass
