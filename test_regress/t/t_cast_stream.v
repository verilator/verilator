// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef enum {
   UVM_TLM_READ_COMMAND,
   UVM_TLM_WRITE_COMMAND,
   UVM_TLM_IGNORE_COMMAND
} uvm_tlm_command_e;

module t(/*AUTOARG*/);

   initial begin
      bit array[] = new [8];
      int unsigned m_length;
      uvm_tlm_command_e m_command;

      m_length = 2;
      array = '{0, 0, 0, 0, 0, 0, 1, 0};
      array = new [$bits(m_length)] (array);
      m_command = uvm_tlm_command_e'({ << bit { array }});

      `checkh(m_command, 'h40)
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
