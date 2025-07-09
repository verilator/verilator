// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class setup_coefficients;
    static function int create();
        return 1;
    endfunction
endclass

class biquad_vseq;
    int c_setup = setup_coefficients::create();
    function void setup_coefficients();
    endfunction
endclass: biquad_vseq
