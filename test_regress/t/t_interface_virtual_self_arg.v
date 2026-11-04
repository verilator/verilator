// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Interfaces whose own scope holds virtual references to the same interface

interface value_if;
  typedef virtual value_if vif_t;

  logic [7:0] value;
  virtual value_if peer;  // Member
  virtual value_if peers[2];  // Unpacked array member
  vif_t typed_peer;  // Typedef member
  inner_if inner ();  // Nested interface referencing this one

  modport mp(input value);

  // Function argument
  function void copy_from(virtual value_if source);
    value = source.value;
  endfunction

  // Modport function argument
  function void copy_from_mp(virtual value_if.mp source);
    value = source.value;
  endfunction

  // Task local variable
  task automatic copy_from_peer();
    virtual value_if local_vif;
    local_vif = peer;
    value = local_vif.value;
  endtask
endinterface

interface inner_if;
  virtual value_if outer;  // Indirect cycle through the nested instance
endinterface

module t;
  value_if a ();
  value_if b ();

  initial begin
    a.value = 8'h11;
    b.copy_from(a);
    `checkh(b.value, 8'h11);

    a.value = 8'h22;
    b.copy_from_mp(a);
    `checkh(b.value, 8'h22);

    a.value = 8'h33;
    b.peer = a;
    b.copy_from_peer();
    `checkh(b.value, 8'h33);

    b.peers[1] = a;
    `checkh(b.peers[1].value, 8'h33);

    b.typed_peer = a;
    `checkh(b.typed_peer.value, 8'h33);

    b.inner.outer = a;
    `checkh(b.inner.outer.value, 8'h33);

    // Self-reference
    a.copy_from(a);
    `checkh(a.value, 8'h33);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
