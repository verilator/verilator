// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Checks that randomize() over a uvm_reg_field-shaped range whose bound shifts
// by a member set at run time reaches the whole solution space. Samples are
// printed so the driver can check uniformity (Jensen-Shannon divergence).
// Widths too large to enumerate are only checked against the range itself.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef logic unsigned [63:0] uvm_reg_data_t;

class uvm_reg_field;
  rand uvm_reg_data_t value;
  int unsigned m_size;
  constraint c_field_valid {
    if (64 > m_size) {
      value < (64'h1 << m_size);
    }
  }
  function void configure(int unsigned size);
    value = 0;
    m_size = size;
  endfunction
endclass

module t;
  localparam int NARROW_SIZE = 6;
  localparam int NUM_SOLUTIONS = 1 << NARROW_SIZE;
  localparam int NUM_ITERS = 25 * NUM_SOLUTIONS;
  localparam int WIDE_ITERS = 100;

  initial begin
    automatic uvm_reg_field narrow = new;
    automatic uvm_reg_field wide[4];
    automatic bit seen[NUM_SOLUTIONS];
    automatic int distinct = 0;
    automatic int ok;

    narrow.configure(NARROW_SIZE);
    foreach (wide[i]) wide[i] = new;
    wide[0].configure(1);
    wide[1].configure(15);
    wide[2].configure(31);
    wide[3].configure(32);

    for (int i = 0; i < NUM_ITERS; ++i) begin
      ok = narrow.randomize();
      `checkd(ok, 1);
      if (!seen[int'(narrow.value)]) begin
        seen[int'(narrow.value)] = 1'b1;
        distinct++;
      end
      $display("%0d", narrow.value);
    end
    `checkd(distinct, NUM_SOLUTIONS);

    // Widths the divergence check cannot enumerate, so only the bound is checked
    foreach (wide[i]) begin
      for (int j = 0; j < WIDE_ITERS; ++j) begin
        ok = wide[i].randomize();
        `checkd(ok, 1);
        `checkd(wide[i].value >> wide[i].m_size, 0);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
