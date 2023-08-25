// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

// Test for bug4281

class CParam #(parameter PARAM=10);
    typedef int type_t;

    function void check_param(int val);
        if (val != PARAM) $stop;
    endfunction
endclass

class CParam2 #(parameter PARAM=10);
    typedef int type_t;

    typedef logic [PARAM-1:0] type2_t;

    function void check_param(int val);
        if (val != PARAM) $stop;
    endfunction
endclass

`ifdef CONSTSIM
module sub();
    parameter N = 32;
    for (genvar i = 0; i < N/8; i = i + 1) begin
        initial begin
        end
    end
    // Test for bug4281, usage conflict of user2 with constant simulator in V3Param.cpp
endmodule
`endif

module t;
`ifdef BAD_PAREN
    CParam::type_t val_0 = 100;
`else
    CParam#()::type_t val_0 = 100;
`endif
    CParam2#()::type_t val_2 = 200;

`ifdef CONSTSIM

    sub i_sub();
`endif

    initial begin
        if (val_0 != 100) $stop;
        if (val_2 != 200) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
