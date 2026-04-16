// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0
// verilog_format: off

typedef logic [31:0] uvm_reg_data_t;

class uvm_object;
endclass

class uvm_reg_field extends uvm_object;
  rand uvm_reg_data_t value;
  int unsigned m_size;

  function uvm_reg_data_t get;
    return value;
  endfunction

  function void set_rand_mode(bit rand_mode);
    value.rand_mode(rand_mode);
    uvm_reg_field_valid.constraint_mode(rand_mode);
  endfunction

  function bit get_rand_mode();
    return bit'(value.rand_mode());
  endfunction

  constraint uvm_reg_field_valid {
    if (64'd64 > {32'd0, m_size}) {
      {32'd0, value} < (64'd1 << m_size);
    }
  }

  function void configure(int unsigned size);
    m_size = size;
  endfunction
endclass

class uvm_reg extends uvm_object;
  virtual function void build();
  endfunction
endclass

class regA extends uvm_reg;
  rand uvm_reg_field fA1;
  rand uvm_reg_field fA2;

  virtual function void build();
    this.fA1 = new;
    this.fA2 = new;
    this.fA1.configure(16);
    this.fA2.configure(16);
  endfunction
endclass

class test extends uvm_object;
  regA rg;

  function new;
    rg = new;
    rg.build();
  endfunction

  task run_test;
    uvm_reg_data_t pre_fA1;
    uvm_reg_data_t pre_fA2;
    int rand_ok;

    // Disable fA1, enable fA2
    rg.fA1.set_rand_mode(0);
    rg.fA2.set_rand_mode(1);

    if (rg.fA1.get_rand_mode() != 0) $stop;
    if (rg.fA2.get_rand_mode() != 1) $stop;

    pre_fA1 = rg.fA1.value;

    rand_ok = rg.randomize();
    if (rand_ok != 0) begin
      // fA1 should be unchanged
      if (rg.fA1.get() !== pre_fA1) begin
        $display("%%Error: fA1 changed: got=%0h exp=%0h", rg.fA1.get(), pre_fA1);
        $stop;
      end
    end

    // Re-enable fA1, disable fA2
    rg.fA1.set_rand_mode(1);
    rg.fA2.set_rand_mode(0);

    pre_fA2 = rg.fA2.value;

    rand_ok = rg.randomize();
    if (rand_ok != 0) begin
      // fA2 should be unchanged
      if (rg.fA2.get() !== pre_fA2) begin
        $display("%%Error: fA2 changed: got=%0h exp=%0h", rg.fA2.get(), pre_fA2);
        $stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  endtask

endclass

module top;
  initial begin
    test t;
    t = new;
    t.run_test();
  end
endmodule
