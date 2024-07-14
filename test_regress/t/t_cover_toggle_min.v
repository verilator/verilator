// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t();
    logic[1:0] a;
    logic[1:0] b;
    logic[1:0] c;

    initial begin
        #1 a = 2'b01;
        #1 b = 2'b10;
        #1 c = 2'b11;
        #1 c = 2'b10;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
