// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

package p;
  typedef enum logic [1:0] {
    A,
    B,
    C,
    D
  } e_t;
  typedef e_t alias_t;
  typedef enum logic [6:0] {
    LOW = 0,
    HIGH = 65
  } wider_t;
  typedef enum logic [1:0] {
    W,
    X,
    Y,
    Z
  } other_t;
endpackage

module t;
  import p::*;
  alias_t ev;
  wider_t wider_ev;
  logic [1:0] bits;
  logic [6:0] wider_bits;
  struct packed {e_t status;} packet;

  task automatic output_bits(output logic [1:0] value);
    value = 2'd3;
  endtask

  task automatic output_other(output other_t value);
    value = Z;
  endtask

  function automatic void function_bits(output logic [1:0] value);
    value = 2'd3;
  endfunction

  task automatic inout_enum(inout e_t value);
    value = C;
  endtask

  task automatic inout_bits(inout logic [1:0] value);
    value = 2'd3;
  endtask

  task automatic input_enum(input e_t value);
  endtask

  task automatic ref_enum(ref e_t value);
    value = C;
  endtask

  initial begin
    // Copying plain logic back to an enum is illegal.
    output_bits(ev);
    // Distinct enums are not implicitly assignment compatible.
    output_other(ev);
    output_bits(packet.status);
    function_bits(ev);
    // The copy-in conversion is illegal.
    inout_enum(bits);
    // The copy-out conversion is illegal.
    inout_bits(ev);
    // Resizing must not hide the enum check.
    inout_enum(wider_bits);
    // Input checks must remain unchanged.
    input_enum(bits);
    // Copy-out must check the original enum lvalue before resizing.
    output_bits(wider_ev);
    inout_bits(wider_ev);
    // Ref arguments still require matching types.
    ref_enum(bits);
  end
endmodule
