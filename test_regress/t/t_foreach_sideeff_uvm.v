// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {int reg_files[int unsigned];} uvm_reg_t;

module t;
  uvm_reg_t blks[int unsigned];

  initial begin
    int sum;
    int inner1_i;
    int inner2_j;

    blks[1].reg_files[10] = 101;
    blks[1].reg_files[11] = 102;
    blks[3].reg_files[20] = 308;
    blks[3].reg_files[21] = 309;

    foreach (blks[i]) begin
      // $display("blks[%d]", i);
      ++inner1_i;
      // This isn't a 2D foreach, but rather a dotted reference using above loop

      // Vlt considers below blks[i]. a side effect because the AstAssocSel can
      // create elements, and threw SIDEEFFECT
      // As this code occurs in UVM, we special case a SIDEEFFECT suppress in
      // verilated_std_waiver.vlt
      // Future alternative is to auto-waiver an ArraySel under another ArraySel
      // with same index in outer loop

      // verilator lint_off SIDEEFFECT
      foreach (blks[i].reg_files[j]) begin
        // verilator lint_on SIDEEFFECT

        ++inner2_j;
        sum += blks[i].reg_files[j];
        // $display("blks[%d].reg_files[%d]", i, j);
      end
    end
    `checkd(inner1_i, 2);
    `checkd(inner2_j, 4);
    `checkd(sum, 820);
    $finish;
  end

endmodule
