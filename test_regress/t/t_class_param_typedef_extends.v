// Reproduction: type parameter lost through typedef extends
//
// When a non-parameterized class extends a typedef of a parameterized class,
// the inner member's type parameter falls back to the default instead of
// inheriting from the typedef's specialization.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;
  class my_item;
    int x;
  endclass

  // Inner parameterized classes
  virtual class if_base #(type T1 = int, type T2 = T1);
  endclass

  virtual class port_base #(type IF = if_base#());
    function void connect(port_base #(IF) other);
    endfunction
  endclass

  class pull_port #(type REQ = int, type RSP = REQ)
    extends port_base #(if_base #(REQ, RSP));
  endclass

  class pull_imp #(type REQ = int, type RSP = REQ, type IMP = int)
    extends port_base #(if_base #(REQ, RSP));
  endclass

  // Outer parameterized class with member using the type param
  class driver #(type REQ = int, type RSP = REQ);
    pull_port #(REQ, RSP) seq_port;
    function new;
      seq_port = new;
    endfunction
  endclass

  // Outer parameterized class on the other side
  class sequencer #(type REQ = int, type RSP = REQ);
    pull_imp #(REQ, RSP, sequencer #(REQ, RSP)) seq_export;
    function new;
      seq_export = new;
    endfunction
  endclass

  // Typedef specialization + extends
  typedef driver #(my_item) my_driver;

  class low_driver extends my_driver;
    function new;
      super.new();
    endfunction
  endclass

  initial begin
    sequencer #(my_item) sqr;
    low_driver drv;

    sqr = new;
    drv = new;

    drv.seq_port.connect(sqr.seq_export);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
