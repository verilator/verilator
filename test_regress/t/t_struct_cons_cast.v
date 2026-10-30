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

    // Constructor items must accept runtime expressions widened by V3Clean.
    begin
      typedef logic [6:0] element_t;
      typedef struct {
        element_t data [2];
        element_t first;
        logic [14:0] second;
      } sample_t;
      element_t assoc[int];
      element_t wildcard_assoc[*];
      element_t dynamic_array[];
      element_t queue[$];
      sample_t result;
      logic [31:0] value;
      repeat (2) begin
        value = $urandom;

        // AstConsArrayItem and AstConsStructItem: cast array elements and scalar members.
        result = '{'{value[6:0], value[13:7]}, value[6:0], value[21:7]};
        `checkh(result.data[0], value[6:0]);
        `checkh(result.data[1], value[13:7]);
        `checkh(result.first, value[6:0]);
        `checkh(result.second, value[21:7]);

        // AstConsAssocItem: entries are constructed through std::pair.
        assoc = '{1: value[6:0], 2: value[13:7], default: value[20:14]};
        `checkh(assoc[1], value[6:0]);
        `checkh(assoc[2], value[13:7]);
        `checkh(assoc[3], value[20:14]);

        // AstConsWildcardItem uses the same entry constructor with string keys.
        wildcard_assoc = '{"first": value[6:0], "second": value[13:7], default: value[20:14]};
        `checkh(wildcard_assoc["first"], value[6:0]);
        `checkh(wildcard_assoc["second"], value[13:7]);
        `checkh(wildcard_assoc["missing"], value[20:14]);

        // AstConsDynArrayItem: positional items, splicing, and sized keyed items.
        dynamic_array = '{value[6:0], value[13:7]};
        `checkh(dynamic_array.size(), 2);
        `checkh(dynamic_array[0], value[6:0]);
        `checkh(dynamic_array[1], value[13:7]);
        dynamic_array = {dynamic_array, value[20:14]};
        `checkh(dynamic_array.size(), 3);
        `checkh(dynamic_array[0], value[6:0]);
        `checkh(dynamic_array[1], value[13:7]);
        `checkh(dynamic_array[2], value[20:14]);
        dynamic_array = new[3] ('{0: value[6:0], 2: value[13:7], default: value[20:14]});
        `checkh(dynamic_array.size(), 3);
        `checkh(dynamic_array[0], value[6:0]);
        `checkh(dynamic_array[1], value[20:14]);
        `checkh(dynamic_array[2], value[13:7]);
        dynamic_array = new[3] ('{0: value[6:0], 2: value[13:7]});
        `checkh(dynamic_array.size(), 3);
        `checkh(dynamic_array[0], value[6:0]);
        `checkh(dynamic_array[1], 7'd0);
        `checkh(dynamic_array[2], value[13:7]);

        // AstConsQueueItem: scalar arguments and a queue to splice.
        queue = '{value[6:0], value[13:7]};
        `checkh(queue.size(), 2);
        `checkh(queue[0], value[6:0]);
        `checkh(queue[1], value[13:7]);
        queue = {value[20:14], queue};
        `checkh(queue.size(), 3);
        `checkh(queue[0], value[20:14]);
        `checkh(queue[1], value[6:0]);
        `checkh(queue[2], value[13:7]);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
