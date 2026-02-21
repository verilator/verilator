// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

// DESCRIPTION: Verilator: Test for cloned RefDType classOrPackagep fix
//
// This test verifies that when parameterized classes are cloned, the RefDType
// nodes that reference typedefs within the class get their classOrPackagep
// and typedefp updated to point to the cloned class, not the template class.
//
// This file is part of the Verilator regression test suite.
//

// A registry class that returns its own type
class uvm_object_registry #(type T = int, string Tname = "<unknown>");
  typedef uvm_object_registry#(T, Tname) this_type;

  static function this_type get();
    static this_type m_inst;
    if (m_inst == null) m_inst = new();
    return m_inst;
  endfunction
endclass

// A pool class that has a nested type_id typedef pointing to the registry
// The key pattern: type_id is a typedef to uvm_object_registry parameterized with THIS class
class uvm_object_string_pool #(type T = int);
  typedef uvm_object_string_pool#(T) this_type;
  typedef uvm_object_registry#(uvm_object_string_pool#(T)) type_id;

  // This function's return type references type_id - after cloning,
  // the RefDType for the return type must point to THIS class's type_id,
  // not the template class's type_id
  static function type_id get_type();
    return type_id::get();
  endfunction

  static function T get_global();
    this_type gpool = new();
    return gpool.get();
  endfunction

  virtual function T get();
    T result;
    return result;
  endfunction
endclass

// Simple wrapper classes to create different specializations
class uvm_queue #(type T = int);
endclass

class uvm_event #(type T = int);
endclass

// Create two different specializations of uvm_object_string_pool
// Each should get its own type_id pointing to a different registry specialization
typedef uvm_object_string_pool#(uvm_event#(int)) uvm_event_pool;
typedef uvm_object_string_pool#(uvm_queue#(string)) uvm_queue_pool;

module t;
  initial begin
    // Get the type_id::get() for both pool types
    // Before the fix, both would incorrectly return the same registry type
    // After the fix, each returns its own correctly-specialized registry

    uvm_object_registry#(uvm_object_string_pool#(uvm_event#(int))) event_reg;
    uvm_object_registry#(uvm_object_string_pool#(uvm_queue#(string))) queue_reg;

    event_reg = uvm_event_pool::get_type();
    queue_reg = uvm_queue_pool::get_type();

    if (event_reg != null && queue_reg != null) begin
      $write("*-* All Coverage Coverage *-*\n");
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
