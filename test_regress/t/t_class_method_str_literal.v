// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

class uvm_reg;
    function int get_1;
        return 1;
    endfunction

    function bit get_true;
        return 1;
    endfunction

    function string get_string;
        if (get_1() == 1) begin
            return get_true() ? "user backdoor" : "DPI backdoor";
        end else begin
            return "";
        end
    endfunction
endclass

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
    uvm_reg u_r = new;
    if (u_r.get_string() != "user backdoor") $stop;
    if (t_c.return_str("A") != "A") $stop;
    if (t_c.static_return_str("B") != "B") $stop;
    if (T::static_return_str("C") != "C") $stop;
    $write("*-* All Finished *-*\n");
    $finish;
end
endmodule
