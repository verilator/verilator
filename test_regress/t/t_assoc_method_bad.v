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
    typedef enum int {
      RED,
      GREEN
    } color_t;
    data_t by_data[data_t];
    int by_class[Base];
    int by_int[int];
    int by_enum[color_t];
    logic [63:0] wider_four_state;
    bit [7:0] narrower;
    Base base_handle;
    Derived derived_handle;
    int int_value;
    color_t enum_value;

    void'(by_data.first(wider_four_state));  // Bad: not equivalent
    void'(by_data.next(narrower));  // Bad: not equivalent
    void'(by_data.last(base_handle));  // Bad: class handle
    void'(by_class.prev(derived_handle));  // Bad: derived class
    void'(by_int.first(enum_value));  // Bad: enum
    void'(by_enum.first(int_value));  // Bad: not an enum
  end
endmodule
