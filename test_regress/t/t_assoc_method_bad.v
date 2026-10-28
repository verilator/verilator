// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  initial begin
    string a[string];
    string k;
    string v;

    v = a.num("badarg");
    v = a.size("badarg");
    v = a.exists();  // Bad
    v = a.exists(k, "bad2");
    v = a.first();  // Bad
    v = a.next(k, "bad2");  // Bad
    v = a.last();  // Bad
    v = a.prev(k, "bad2");  // Bad
    a.delete(k, "bad2");

    a.sort;  // Not legal on assoc
    a.rsort;  // Not legal on assoc
    a.reverse;  // Not legal on assoc
    a.shuffle;  // Not legal on assoc

    a.bad_not_defined();
  end

  class Base;
  endclass

  class Derived extends Base;
  endclass

  initial begin
    typedef bit [31:0] data_t;
    data_t by_data[data_t];
    int by_class[Base];
    data_t same_type;
    bit [3:0][7:0] equivalent_type;
    logic [63:0] wider_four_state;
    bit [7:0] narrower;
    Base base_handle;
    Derived derived_handle;

    void'(by_data.first(same_type));
    void'(by_data.next(equivalent_type));
    void'(by_class.first(base_handle));

    void'(by_data.first(wider_four_state));  // Bad: not equivalent
    void'(by_data.next(narrower));  // Bad: not equivalent
    void'(by_data.last(base_handle));  // Bad: class handle
    void'(by_class.prev(derived_handle));  // Bad: derived class
  end
endmodule
