// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// Inherited methods that must not count as interface class implementations.

interface class top_if;
  pure virtual function int get_a();
endclass

// Bad: inherited method is itself pure virtual
virtual class abstract_cls;
  pure virtual function int get_a();
endclass

class from_abstract_cls extends abstract_cls implements top_if;
endclass

// Bad: inherited method is static
class static_cls;
  static function int get_a();
    return 1;
  endfunction
endclass

class from_static_cls extends static_cls implements top_if;
endclass

// Bad: inherited method is not virtual (IEEE 1800-2023 8.26.2)
class nonvirtual_cls;
  function int get_a();
    return 2;
  endfunction
endclass

class from_nonvirtual_cls extends nonvirtual_cls implements top_if;
endclass

module t;
endmodule
