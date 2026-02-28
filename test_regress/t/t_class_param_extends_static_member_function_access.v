// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

class Class1 #(
    type T
);
  static function int get_p();
    return 7;
  endfunction
endclass

class Class2 #(
    type T
) extends Class1 #(T);
  static function int get_p2;
    return T::get_p();
  endfunction
endclass

module t;
  initial begin
    typedef Class2#(Class1#(int)) Class;
    if (Class::get_p2() != Class1#(int)::get_p()) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
