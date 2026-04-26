// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  class uvm_object;
  endclass

  class uvm_typeid_base;
  endclass

  class uvm_typeid #(
      type T = uvm_object
  ) extends uvm_typeid_base;
    static uvm_typeid #(T) m_b_inst;
    static function uvm_typeid#(T) get();
      if (m_b_inst == null) begin
        m_b_inst = new;
      end
      return m_b_inst;
    endfunction
  endclass

  class base_cmp extends uvm_object;
  endclass

  class base_oth extends uvm_object;
  endclass

  initial begin
    string sc1, sc2, so;

    // IEEE 1800-2023 21.2.1.1 suggests %d of a class is illegal.
    // Howver UVM tests require %0d print unique identifier of the class.
    // In contrast, %x of a class reference, causes errors on several simulators.
    $display("BASE_CMP: %%p=%p", uvm_typeid#(base_cmp)::get());
    $display("BASE_CMP: %%0d=%0d", uvm_typeid#(base_cmp)::get());
    $display("BASE_OTH: %%p=%p", uvm_typeid#(base_oth)::get());
    $display("BASE_OTH: %%0d=%0d", uvm_typeid#(base_oth)::get());

    sc1 = $sformatf(": %0d", uvm_typeid#(base_cmp)::get());
    sc2 = $sformatf(": %0D", uvm_typeid#(base_cmp)::get());
    so = $sformatf(": %0d", uvm_typeid#(base_oth)::get());
    if (sc1 != sc2) begin
      $display("Expected class-to-%%d strings to be ==\n  sc1=%s\n  sc2=%s", sc1, sc2);
      $stop;
    end
    // TODO make a unique identifier
    // Complication is runtime of %p vs %d; need to pass both string and object?
    // if (sc1 == so) begin
    //   $display("Expected class-to-%%d strings to be !=\n  sc1=%s\n  so=%s", sc1, so);
    //   $stop;
    // end

    $finish;
  end
endmodule
