// DESCRIPTION: Verilator: Verilog Test module
//
// SPDX-FileCopyrightText: 2026 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

// Overriding a type parameter whose default is a parameterized class scope
// still specializes the class, so its body must be elaborated (#8440).

package pkg;
  function automatic integer func();
    return 1;
  endfunction
endpackage

class class_with_package_call #(
    parameter int unused_param = 0
);
  typedef int value_t;
  localparam int local_param = pkg::func();
endclass

module module_with_type_parameter #(
    parameter type value_t = class_with_package_call#(0)::value_t
);
endmodule

interface iface_with_type_parameter #(
    parameter type value_t = class_with_package_call#(1)::value_t
) ();
  value_t value;
endinterface

module top;
  module_with_type_parameter #(.value_t(logic signed [15:0])) dut ();
  iface_with_type_parameter #(.value_t(logic signed [15:0])) itf ();
endmodule
