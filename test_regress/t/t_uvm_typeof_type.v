// DESCRIPTION: Verilator: Verify that nested class type parameters with
// explicit-equivalent defaults resolve to the same specialization.
//
// When uvm_reg_sequence#(type BASE = uvm_sequence#(uvm_reg_item)) is
// extended with the explicit equivalent default, both must produce the
// same specialization so that $cast succeeds between them.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

virtual class uvm_object;
endclass

class uvm_factory;
  uvm_object m_type_names[string];

  function uvm_object create_object_by_name(string name);
    uvm_object wrapper;
    if (m_type_names.exists(name)) begin
      wrapper = m_type_names[name];
    end
    else begin
      $display("%%Error: object not found '%s'", name);
      $stop;
    end
    return wrapper;
  endfunction

  function void register(uvm_object obj, string name);
    m_type_names[name] = obj;
  endfunction
endclass

uvm_factory factory;

class uvm_sequence_item extends uvm_object;
endclass

class uvm_reg_item extends uvm_sequence_item;
endclass

virtual class uvm_sequence #(
  type REQ = uvm_sequence_item,
  type RSP = REQ
) extends uvm_object;
endclass

class uvm_reg_sequence #(
  type BASE = uvm_sequence#(uvm_reg_item)
) extends BASE;
  function new;
    factory.register(this, "uvm_reg_sequence");
  endfunction
endclass

class uvm_reg_hw_reset_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));
  function new;
    factory.register(this, "uvm_reg_hw_reset_seq");
  endfunction
endclass

module t;
  initial begin
    uvm_reg_hw_reset_seq rsq;

    uvm_reg_sequence seq;
    uvm_object obj;
    int cst;
    string seq_name;

    factory = new;
    rsq = new;

    seq_name = "uvm_reg_hw_reset_seq";

    obj = factory.create_object_by_name(seq_name);
    if (obj == null) $stop;

    cst = $cast(seq, obj);
    /* verilator lint_off WIDTHTRUNC */
    if (!cst || seq == null) begin
      $display("%%Error: cast failed");
      $stop;
    end
    /* verilator lint_on WIDTHTRUNC */
    if (seq != rsq) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
