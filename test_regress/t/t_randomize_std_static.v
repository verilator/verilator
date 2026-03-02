// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test std::randomize() called from a static function referencing static
// class members in the 'with' clause.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  typedef enum bit [3:0] {
    INSTR_ADD = 0,
    INSTR_SUB = 1,
    INSTR_MUL = 2,
    INSTR_AND = 4
  } instr_name_t;

  class instr_base;
    static instr_name_t allowed_instrs[$];

    static function void init();
      allowed_instrs.push_back(INSTR_ADD);
      allowed_instrs.push_back(INSTR_SUB);
      allowed_instrs.push_back(INSTR_MUL);
      allowed_instrs.push_back(INSTR_AND);
    endfunction

    static function instr_name_t get_rand_instr();
      instr_name_t name;
      int ok;
      ok = std::randomize(name) with {
        name inside {allowed_instrs};
      };
      `checkd(ok, 1);
      return name;
    endfunction
  endclass

  initial begin
    instr_name_t result;

    instr_base::init();

    repeat (20) begin
      result = instr_base::get_rand_instr();
      `checkd(result == INSTR_ADD || result == INSTR_SUB
              || result == INSTR_MUL || result == INSTR_AND, 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
