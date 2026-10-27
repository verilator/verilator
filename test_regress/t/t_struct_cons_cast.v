// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

class uvm_policy;
  typedef enum {
    NEVER,
    STARTED,
    FINISHED
  } recursion_state_e;
endclass

typedef enum {
  UVM_DEFAULT_POLICY = 0,
  UVM_DEEP = (1 << 16),
  UVM_SHALLOW = (1 << 17),
  UVM_REFERENCE = (1 << 18)
} uvm_recursion_policy_enum;

class Cls;
  typedef struct {
    uvm_policy::recursion_state_e state;
    bit ret_val;
  } state_info_t;

  state_info_t m_recur_states/*[uvm_object][uvm_object]*/ [uvm_recursion_policy_enum];

  function uvm_recursion_policy_enum get_recursion_policy();
    return UVM_DEEP;
  endfunction

  function bit get_ret_val();
    return $c(1);
  endfunction

  function void test();
    bit ret_val;
    ret_val = $c1(1);
    // See issue #4568
    m_recur_states[get_recursion_policy()] = '{uvm_policy::FINISHED, ret_val};
  endfunction

endclass

module t;

  initial begin
    Cls c;
    c = new;
    $display("%p", c);

    // Nested array constructor elements also need casts to their C++ storage type.
    begin
      typedef struct {
        logic [6:0] data [2];
      } sample_t;
      sample_t result;
      logic [31:0] value;
      repeat (10) begin
        value = $urandom;
        result = '{'{value[6:0], value[13:7]}};
        `checkh(result.data[0], value[6:0]);
        `checkh(result.data[1], value[13:7]);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
