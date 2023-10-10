// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

/// (See bug4551)
/// Verilator creates an AstEnumItemRef for each reference. If the enum is inside a parameterizable class/module, it
/// should be handled properly.

class ClsParam #(
   int A = 0
);
    typedef enum int {
        EN_A = A + 0,
        EN_B = A + 1,
        EN_C = A + 2
    } enums_t;

    int val = EN_C;
    function int test();
        return EN_C;
    endfunction
endclass;

module t;
    // localparam ENUM_VAL = ClsParam#(100)::EN_C; // TODO: Unsupported: dotted expressions in parameters
    // $info("ENUM_VAL: %0d", ENUM_VAL);

    ClsParam#(100) cls = new;
    initial begin
        if (cls.test() != 102) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
