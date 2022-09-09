// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

class T;
    function automatic void print_str(input string a_string);
        $display(a_string);
    endfunction

    static function automatic void static_print_str(input string a_string);
        $display(a_string);
    endfunction
endclass


initial begin
    T t_c = new;
    t_c.print_str("function though member");
    t_c.static_print_str("static function through member");
    T::static_print_str("static function through class");
    $write("*-* All Finished *-*\n");
    $finish;
end
endmodule
