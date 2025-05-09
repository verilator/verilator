// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

class cls;
    int field_val;
endclass

module t();
    cls inst[1];

    initial begin
        // Loop (even just 1 iteration) is needed to reproduce the error
        for(int i = 0; i < 1; i++) begin
            inst[i]           = new();
            inst[i].field_val = 1;
        end
        $finish;
    end
endmodule
