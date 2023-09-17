// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

class T;
    function automatic string return_str(input string a_string);
       return a_string;
    endfunction

    static function automatic string static_return_str(input string a_string);
        return a_string;
    endfunction
endclass


initial begin
    T t_c = new;
    if (t_c.return_str("A") != "A") $stop;
    if (t_c.static_return_str("B") != "B") $stop;
    if (T::static_return_str("C") != "C") $stop;
    $write("*-* All Finished *-*\n");
    $finish;
end
endmodule
