// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Robert Newgard.
// SPDX-License-Identifier: CC0-1.0

package t_pkg;
    typedef enum [1:0]
    {
        ENUM_1_0,
        ENUM_1_1,
        ENUM_1_2,
        ENUM_1_3
    }
    t_enum_1;

    typedef enum logic [1:0]
    {
        ENUM_2_0,
        ENUM_2_1,
        ENUM_2_2,
        ENUM_2_3
    }
    t_enum_2;
endpackage

module t();
    typedef enum logic [1:0]
    {
        ENUM_3_0,
        ENUM_3_1,
        ENUM_3_2,
        ENUM_3_3
    }
    t_enum_3;

    initial begin
        $write("*-* All Finished *-*\n");
        $finish();
    end
endmodule
