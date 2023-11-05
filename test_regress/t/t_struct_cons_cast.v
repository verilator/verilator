// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class uvm_policy;
   typedef enum {
                 NEVER,
                 STARTED,
                 FINISHED
                 } recursion_state_e;
endclass

typedef enum {
              UVM_DEFAULT_POLICY = 0,
              UVM_DEEP           = (1<<16),
              UVM_SHALLOW        = (1<<17),
              UVM_REFERENCE      = (1<<18)
              } uvm_recursion_policy_enum;

class Cls;
   typedef struct {
      uvm_policy::recursion_state_e state;
      bit         ret_val;
   } state_info_t;

   state_info_t m_recur_states/*[uvm_object][uvm_object]*/[uvm_recursion_policy_enum];

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
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
